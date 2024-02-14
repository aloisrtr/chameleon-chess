//! Main API to represent and interact with a chess position.
//!
//! This includes making, unmaking and generating moves, defining positions from
//! FEN strings, etc.
use std::hint::unreachable_unchecked;

use arrayvec::ArrayVec;

use crate::{
    bitboard::Bitboard,
    lookup_tables::*,
    r#move::{LegalMove, Move},
    square::{Delta, File, Rank, Square},
};

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub struct IllegalMoveError;

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
// TODO: Better FEN parsing error reports.
/// FEN parsing errors.
pub enum FenError {
    UnexpectedToken { index: usize, val: char },
    Incomplete,
    NonAscii,
    ParseError,
    IncompletePieceSection,
}

/// Records non-reversible informations that are lost when making a move.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
struct HistoryEntry {
    pub played: LegalMove,
    pub captured: Option<PieceKind>,
    pub castling_rights: u8,
    pub reversible_moves: u8,
    pub en_passant_file: Option<File>,
    pub hash: u64,
}

/// Existing types of pieces.
#[repr(u8)]
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum PieceKind {
    Pawn = 0,
    Knight = 1,
    Bishop = 2,
    Rook = 3,
    Queen = 4,
    King = 5,
}
impl PieceKind {
    /// Checks if this piece kind is a diagonal slider.
    #[inline(always)]
    pub fn is_diagonal_slider(self) -> bool {
        (self as u8 + 3) & 0b101 == 0b101
    }
    /// Checks if this piece kind is an orthogonal slider.
    #[inline(always)]
    pub fn is_orthogonal_slider(self) -> bool {
        (self as u8 + 3) & 0b110 == 0b110
    }
}
impl std::fmt::Display for PieceKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Pawn => 'p',
                Self::Knight => 'n',
                Self::Bishop => 'b',
                Self::Rook => 'r',
                Self::Queen => 'q',
                Self::King => 'k',
            }
        )
    }
}

/// Represents a valid chess position and defines an API to interact with said
/// position (making, unmaking, generating moves, etc).
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Position {
    // 8x8 array to find which piece sits on which square.
    pieces: [Option<PieceKind>; 64],
    // Bitboards are indexed by piece kind.
    piece_bitboards: [Bitboard; 6],
    // Bitboards containing occupancy information by color.
    color_bitboards: [Bitboard; 2],
    // Bitboard containing occupancy information.
    occupancy_bitboard: Bitboard,

    // Metadata
    black_to_move: bool,
    castling_rights: u8,
    reversible_moves: u8,
    en_passant_file: Option<File>,
    history: ArrayVec<HistoryEntry, 1024>,
    hash: u64,
}
impl Default for Position {
    /// A position with no pieces.
    fn default() -> Self {
        Self {
            pieces: [None; 64],
            piece_bitboards: [Bitboard::empty(); 6],
            color_bitboards: [Bitboard::empty(); 2],
            occupancy_bitboard: Bitboard::empty(),

            black_to_move: false,
            castling_rights: 0b1111,
            reversible_moves: 0,
            en_passant_file: None,
            history: ArrayVec::new(),
            hash: 0,
        }
    }
}
impl Position {
    /// A position with no pieces.
    pub fn empty() -> Self {
        Self::default()
    }

    /// The initial position of chess.
    pub fn initial() -> Self {
        Self::from_fen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1").unwrap()
    }

    /// Creates a position from a FEN string.
    /// # Errors
    /// This function returns an error if the FEN string passed is invalid or badly
    /// formatted.
    pub fn from_fen(fen: &str) -> Result<Self, FenError> {
        if !fen.is_ascii() {
            return Err(FenError::NonAscii);
        }

        let mut position = Self::empty();

        let sections = fen.split_ascii_whitespace().collect::<Vec<_>>();
        let pieces = sections.first().ok_or(FenError::Incomplete)?;
        let mut squares = Square::squares_fen_iter();
        for c in pieces.chars() {
            let black = c.is_ascii_lowercase();
            unsafe {
                match c.to_ascii_lowercase() {
                    'p' => position.add_piece_unchecked(
                        squares.next().ok_or(FenError::IncompletePieceSection)?,
                        PieceKind::Pawn,
                        black,
                    ),
                    'n' => position.add_piece_unchecked(
                        squares.next().ok_or(FenError::IncompletePieceSection)?,
                        PieceKind::Knight,
                        black,
                    ),
                    'b' => position.add_piece_unchecked(
                        squares.next().ok_or(FenError::IncompletePieceSection)?,
                        PieceKind::Bishop,
                        black,
                    ),
                    'r' => position.add_piece_unchecked(
                        squares.next().ok_or(FenError::IncompletePieceSection)?,
                        PieceKind::Rook,
                        black,
                    ),
                    'q' => position.add_piece_unchecked(
                        squares.next().ok_or(FenError::IncompletePieceSection)?,
                        PieceKind::Queen,
                        black,
                    ),
                    'k' => position.add_piece_unchecked(
                        squares.next().ok_or(FenError::IncompletePieceSection)?,
                        PieceKind::King,
                        black,
                    ),
                    '/' => continue,
                    digit if digit.is_ascii_digit() => {
                        let skip = digit.to_digit(10).unwrap() as usize;
                        if skip > 8 {
                            return Err(FenError::UnexpectedToken {
                                index: 0,
                                val: digit,
                            });
                        }
                        for _ in 0..skip {
                            squares.next();
                        }
                    }
                    c => return Err(FenError::UnexpectedToken { index: 0, val: c }),
                }
            }
        }

        position.black_to_move = match *sections.get(1).ok_or(FenError::Incomplete)? {
            "w" => false,
            "b" => {
                position.hash ^= Self::side_to_move_hash();
                true
            }
            _ => return Err(FenError::UnexpectedToken { index: 0, val: '0' }),
        };

        position.castling_rights = {
            let mut rights = 0;
            let mut empty = false;
            for c in sections.get(2).ok_or(FenError::Incomplete)?.chars() {
                match c {
                    'k' => {
                        position.hash ^= Self::kingside_right_hash::<true>();
                        rights |= 0b0001
                    }
                    'q' => {
                        position.hash ^= Self::queenside_right_hash::<true>();
                        rights |= 0b0010
                    }
                    'K' => {
                        position.hash ^= Self::kingside_right_hash::<false>();
                        rights |= 0b0100
                    }
                    'Q' => {
                        position.hash ^= Self::queenside_right_hash::<false>();
                        rights |= 0b1000
                    }
                    '-' => empty = true,
                    c => return Err(FenError::UnexpectedToken { index: 0, val: c }),
                }
            }

            if (rights == 0) ^ empty {
                return Err(FenError::ParseError);
            }
            rights
        };

        position.en_passant_file = match *sections.get(3).ok_or(FenError::Incomplete)? {
            "-" => None,
            s => {
                let file = s
                    .parse::<Square>()
                    .map_err(|_| FenError::ParseError)?
                    .file();
                position.hash ^= Self::en_passant_file_hash(file);
                Some(file)
            }
        };

        position.reversible_moves = sections.get(4).unwrap_or(&"0").parse().unwrap();

        Ok(position)
    }

    /// Returns a FEN string describing the position.
    pub fn fen(&self) -> String {
        todo!()
    }

    /// Adds a piece on the board on the given square.
    /// # Safety
    /// Placing a piece on an occupied square will result in undefined behavior.
    pub unsafe fn add_piece_unchecked(&mut self, on: Square, kind: PieceKind, black: bool) {
        self.piece_bitboards[kind as usize] |= on.bitboard();
        self.color_bitboards[black as usize] |= on.bitboard();
        self.occupancy_bitboard |= on.bitboard();
        self.pieces[on as usize] = Some(kind);

        self.hash ^= if black {
            Self::piece_hash::<true>(kind, on)
        } else {
            Self::piece_hash::<false>(kind, on)
        }
    }

    /// Returns the piece kind and color sitting on a given square if any.
    pub fn piece_on(&self, square: Square) -> Option<(PieceKind, bool)> {
        self.pieces[square as usize].map(|kind| (kind, self.color_bitboards[1].is_set(square)))
    }

    /// Makes a move on the board, modifying the position.
    /// # Errors
    /// This function returns an error if the move is illegal.
    pub fn make(
        &mut self,
        Move {
            origin,
            target,
            promotion,
        }: Move,
    ) -> Result<(), IllegalMoveError> {
        if let Some(&mv) = self.moves().iter().find(|mv| {
            mv.origin() == origin && mv.target() == target && mv.is_promotion() == promotion
        }) {
            unsafe { self.make_unchecked(mv) };
            Ok(())
        } else {
            Err(IllegalMoveError)
        }
    }

    /// Makes a move on the board, modifying the position.
    /// # Safety
    /// Trying to play an illegal move will result in undefined behavior as it will
    /// mess up invariants of the inner board representation.
    ///
    /// As a general rule of thumb, only use this function with moves generated
    /// from the position as they are guaranteed to be legal.
    #[inline]
    pub unsafe fn make_unchecked(&mut self, mv: LegalMove) {
        #[inline(always)]
        unsafe fn make_unchecked_generic<const BLACK_TO_MOVE: bool>(
            position: &mut Position,
            mv: LegalMove,
        ) {
            let origin = mv.origin();
            let target = mv.target();
            let move_bitboard = origin.bitboard() | target.bitboard();
            let Some(mut moving_kind) = position.pieces.get_unchecked(origin as usize) else {
                unreachable_unchecked()
            };

            let us_index = BLACK_TO_MOVE as usize;
            let them_index = !BLACK_TO_MOVE as usize;

            position.history.push_unchecked(HistoryEntry {
                played: mv,
                captured: *position.pieces.get_unchecked(target as usize),
                castling_rights: position.castling_rights,
                reversible_moves: position.reversible_moves,
                en_passant_file: position.en_passant_file,
                hash: position.hash,
            });

            // Reset en passant file if any
            if let Some(en_passant_file) = position.en_passant_file.take() {
                position.hash ^= Position::en_passant_file_hash(en_passant_file)
            }

            // Modify castling rights if needed
            // TODO: update hash
            for modified in move_bitboard & Bitboard(0x9100000000000091) {
                match modified {
                    Square::E1 => position.castling_rights &= !0b1100,
                    Square::A1 => position.castling_rights &= !0b1000,
                    Square::H1 => position.castling_rights &= !0b0100,
                    Square::E8 => position.castling_rights &= !0b0011,
                    Square::A8 => position.castling_rights &= !0b0010,
                    Square::H8 => position.castling_rights &= !0b0001,
                    _ => unreachable_unchecked(),
                }
            }

            // Take care of move kind specifics
            if let Some(to) = mv.is_promotion() {
                *position
                    .piece_bitboards
                    .get_unchecked_mut(PieceKind::Pawn as usize) ^= origin.bitboard();
                *position.piece_bitboards.get_unchecked_mut(to as usize) ^= origin.bitboard();
                *position.pieces.get_unchecked_mut(origin as usize) = Some(to);
                position.hash ^= Position::piece_hash::<BLACK_TO_MOVE>(moving_kind, origin);
                position.hash ^= Position::piece_hash::<BLACK_TO_MOVE>(to, origin);
                moving_kind = to;

                if mv.is_capture() {
                    let Some(captured) = *position.pieces.get_unchecked(target as usize) else {
                        unreachable_unchecked()
                    };
                    *position.color_bitboards.get_unchecked_mut(them_index) ^= target.bitboard();
                    *position
                        .piece_bitboards
                        .get_unchecked_mut(captured as usize) ^= target.bitboard();
                    position.occupancy_bitboard ^= target.bitboard();
                    if BLACK_TO_MOVE {
                        position.hash ^= Position::piece_hash::<false>(captured, target);
                    } else {
                        position.hash ^= Position::piece_hash::<true>(captured, target);
                    }
                }
                position.reversible_moves = 0
            } else if mv.is_capture() {
                let target = if mv.special_0_is_set() {
                    target.translate_unchecked(if BLACK_TO_MOVE {
                        Delta::North
                    } else {
                        Delta::South
                    })
                } else {
                    target
                };
                let Some(captured) = *position.pieces.get_unchecked(target as usize) else {
                    unreachable_unchecked()
                };
                *position.color_bitboards.get_unchecked_mut(them_index) ^= target.bitboard();
                *position
                    .piece_bitboards
                    .get_unchecked_mut(captured as usize) ^= target.bitboard();
                position.occupancy_bitboard ^= target.bitboard();
                if BLACK_TO_MOVE {
                    position.hash ^= Position::piece_hash::<false>(captured, target);
                } else {
                    position.hash ^= Position::piece_hash::<true>(captured, target);
                }
                position.reversible_moves = 0
            } else if mv.special_1_is_set() {
                let (rook_origin, rook_target) = if mv.special_0_is_set() {
                    if BLACK_TO_MOVE {
                        (Square::A8, Square::D8)
                    } else {
                        (Square::A1, Square::D1)
                    }
                } else if BLACK_TO_MOVE {
                    (Square::H8, Square::F8)
                } else {
                    (Square::H1, Square::F1)
                };
                let rook_move = rook_origin.bitboard() | rook_target.bitboard();
                *position
                    .piece_bitboards
                    .get_unchecked_mut(PieceKind::Rook as usize) ^= rook_move;
                *position.color_bitboards.get_unchecked_mut(us_index) ^= rook_move;
                position.occupancy_bitboard ^= rook_move;
                *position.pieces.get_unchecked_mut(rook_target as usize) = position
                    .pieces
                    .get_unchecked_mut(rook_origin as usize)
                    .take();
                position.hash ^=
                    Position::piece_hash::<BLACK_TO_MOVE>(PieceKind::Rook, rook_origin);
                position.hash ^=
                    Position::piece_hash::<BLACK_TO_MOVE>(PieceKind::Rook, rook_target);
                position.reversible_moves = 0
            } else if mv.special_0_is_set() {
                position.en_passant_file = Some(origin.file());
                position.hash ^= Position::en_passant_file_hash(origin.file());
                position.reversible_moves = 0
            } else if moving_kind != PieceKind::Pawn {
                position.reversible_moves += 1
            } else {
                position.reversible_moves = 0
            }

            // Then make the actual move on the board
            *position.color_bitboards.get_unchecked_mut(us_index) ^= move_bitboard;
            *position
                .piece_bitboards
                .get_unchecked_mut(moving_kind as usize) ^= move_bitboard;
            position.occupancy_bitboard ^= move_bitboard;
            *position.pieces.get_unchecked_mut(target as usize) =
                position.pieces.get_unchecked_mut(origin as usize).take();
            position.hash ^= Position::piece_hash::<BLACK_TO_MOVE>(moving_kind, origin);
            position.hash ^= Position::piece_hash::<BLACK_TO_MOVE>(moving_kind, target);

            position.black_to_move = !BLACK_TO_MOVE;
            position.hash ^= Position::side_to_move_hash();
        }

        if self.black_to_move {
            make_unchecked_generic::<true>(self, mv);
        } else {
            make_unchecked_generic::<false>(self, mv);
        }
    }

    /// Undoes the effects of the last move played, restoring the position as it
    /// was prior to the move.
    ///
    /// If no moves were played prior to calling this function, nothing happens.
    #[inline]
    pub fn unmake(&mut self) {
        #[inline(always)]
        unsafe fn unmake_generic<const BLACK_TO_MOVE: bool>(
            position: &mut Position,
            HistoryEntry {
                played,
                captured,
                castling_rights,
                reversible_moves,
                en_passant_file,
                hash,
            }: HistoryEntry,
        ) {
            let us_index = BLACK_TO_MOVE as usize;
            let them_index = !BLACK_TO_MOVE as usize;

            // Restore metadata
            position.castling_rights = castling_rights;
            position.reversible_moves = reversible_moves;
            position.en_passant_file = en_passant_file;
            position.black_to_move = BLACK_TO_MOVE;
            position.hash = hash;

            // Unmake the move
            let origin = played.origin();
            let target = played.target();
            let move_bitboard = origin.bitboard() | target.bitboard();
            unsafe {
                *position.pieces.get_unchecked_mut(origin as usize) =
                    position.pieces.get_unchecked_mut(target as usize).take()
            };
            let Some(moving_kind) = position.pieces[origin as usize] else {
                unreachable_unchecked()
            };
            *position.color_bitboards.get_unchecked_mut(us_index) ^= move_bitboard;
            *position
                .piece_bitboards
                .get_unchecked_mut(moving_kind as usize) ^= move_bitboard;
            position.occupancy_bitboard ^= move_bitboard;

            // And deal with move kind specifics
            if let Some(to) = played.is_promotion() {
                *position
                    .piece_bitboards
                    .get_unchecked_mut(PieceKind::Pawn as usize) ^= origin.bitboard();
                *position.piece_bitboards.get_unchecked_mut(to as usize) ^= origin.bitboard();
                *position.pieces.get_unchecked_mut(origin as usize) = Some(PieceKind::Pawn);

                if played.is_capture() {
                    let Some(captured) = captured else {
                        unreachable_unchecked()
                    };
                    *position.color_bitboards.get_unchecked_mut(them_index) ^= target.bitboard();
                    *position
                        .piece_bitboards
                        .get_unchecked_mut(captured as usize) ^= target.bitboard();
                    position.occupancy_bitboard ^= target.bitboard();
                    *position.pieces.get_unchecked_mut(target as usize) = Some(captured);
                }
            } else if played.is_capture() {
                let target = if played.special_0_is_set() {
                    unsafe {
                        target.translate_unchecked(if BLACK_TO_MOVE {
                            Delta::North
                        } else {
                            Delta::South
                        })
                    }
                } else {
                    target
                };
                let captured = captured.unwrap_or(PieceKind::Pawn);
                *position.color_bitboards.get_unchecked_mut(them_index) ^= target.bitboard();
                *position
                    .piece_bitboards
                    .get_unchecked_mut(captured as usize) ^= target.bitboard();
                position.occupancy_bitboard ^= target.bitboard();
                *position.pieces.get_unchecked_mut(target as usize) = Some(captured);
            } else if played.special_1_is_set() {
                let (rook_origin, rook_target) = if played.special_0_is_set() {
                    if BLACK_TO_MOVE {
                        (Square::A8, Square::D8)
                    } else {
                        (Square::A1, Square::D1)
                    }
                } else if BLACK_TO_MOVE {
                    (Square::H8, Square::F8)
                } else {
                    (Square::H1, Square::F1)
                };
                let rook_move = rook_origin.bitboard() | rook_target.bitboard();
                *position
                    .piece_bitboards
                    .get_unchecked_mut(PieceKind::Rook as usize) ^= rook_move;
                *position.color_bitboards.get_unchecked_mut(us_index) ^= rook_move;
                position.occupancy_bitboard ^= rook_move;
                unsafe {
                    *position.pieces.get_unchecked_mut(rook_origin as usize) = position
                        .pieces
                        .get_unchecked_mut(rook_target as usize)
                        .take()
                };
            }
        }

        if let Some(history_entry) = self.history.pop() {
            unsafe {
                if self.black_to_move {
                    unmake_generic::<false>(self, history_entry)
                } else {
                    unmake_generic::<true>(self, history_entry)
                }
            }
        }
    }

    /// Generates a list of legal moves in the current position.
    ///
    /// If this function returns an empty list, the side to move is in checkmate.
    pub fn moves(&self) -> ArrayVec<LegalMove, 256> {
        #[inline(always)]
        unsafe fn moves_generic<const BLACK_TO_MOVE: bool>(
            position: &Position,
        ) -> ArrayVec<LegalMove, 256> {
            let mut moves = ArrayVec::new();

            // Initialize some generally useful constants.
            let us_index = BLACK_TO_MOVE as usize;
            let them_index = !BLACK_TO_MOVE as usize;

            let mut us = position.color_bitboards[us_index];
            let them = position.color_bitboards[them_index];

            let (pawn_push, pawn_east_attack, pawn_west_attack, promotion_rank, double_push_rank) =
                if BLACK_TO_MOVE {
                    (
                        Delta::South,
                        Delta::SouthEast,
                        Delta::SouthWest,
                        Rank::Two.bitboard(),
                        Rank::Six.bitboard(),
                    )
                } else {
                    (
                        Delta::North,
                        Delta::NorthEast,
                        Delta::NorthWest,
                        Rank::Seven.bitboard(),
                        Rank::Three.bitboard(),
                    )
                };

            let king = position.piece_bitboards[PieceKind::King as usize] & us;
            let king_square = king.lowest_set_square_unchecked();

            // Test for absolute pins and attacks.
            // We generate moves for pinned pieces directly when detecting them. Those
            // pieces are masked from bitboards afterwards.

            // If we find a direct attack to the king, we can now ignore absolutely
            // pinned pieces since their moves are known to be illegal anyway

            // Represents the checkers, or squares containing opponent pieces if none is found.
            let mut capturable = Bitboard::empty();
            // Represents the check rays, empty squares otherwise.
            let mut movable = Bitboard::empty();
            // Squares attacked by enemy pieces.
            let mut attacked = Bitboard::empty();

            // First, fill the `attacked` board with info from direct contact pieces.
            // Those pieces do not generate rays and thus cannot be blocked or create pins.
            let ennemy_pawns = position.piece_bitboards[PieceKind::Pawn as usize] & them;
            attacked |= ((ennemy_pawns & !File::H.bitboard()) - pawn_west_attack)
                | ((ennemy_pawns & !File::A.bitboard()) - pawn_east_attack);

            let ennemy_knights = position.piece_bitboards[PieceKind::Knight as usize] & them;
            // TODO: Parallel generation of knight attacks using SIMD
            for origin in ennemy_knights {
                attacked |= Position::knight_moves(origin)
            }

            // If any of those attacked squares intersects with our king, we find the checkers
            // and add them to the `capturable` set.
            if attacked.intersects(king) {
                capturable |= Position::knight_moves(king_square) & ennemy_knights;
                capturable |= (((king & !File::H.bitboard()) + pawn_east_attack)
                    | ((king & !File::A.bitboard()) + pawn_west_attack))
                    & ennemy_pawns;
            }

            // The enemy king cannot check us legally,
            // but we still need to compute the squares it attacks.
            attacked |= Position::king_moves(
                (position.piece_bitboards[PieceKind::King as usize] & them)
                    .lowest_set_square_unchecked(),
            );

            // We then deal with ray attacks. These can produce pins and are blockable.
            // For each sliding piece, we generate its moves and then check for two scenarios:
            // - either the piece directly attacks our king, we're in check and add the slider to the `capturable` set.
            // - or the piece can attack our king when xraying our pieces. In this case, the slider might create a pin.

            // We need to xray our king to account for slide-aways attacked squares.
            let non_king = position.occupancy_bitboard ^ king;

            // Diagonal attacks
            let ennemy_bishops = position.piece_bitboards[PieceKind::Bishop as usize] & them;
            let ennemy_rooks = position.piece_bitboards[PieceKind::Rook as usize] & them;
            let ennemy_queens = position.piece_bitboards[PieceKind::Queen as usize] & them;

            let ennemy_diagonals = ennemy_queens | ennemy_bishops;
            let ennemy_orthogonals = ennemy_rooks | ennemy_queens;

            let king_diagonal_rays = Position::diagonal_moves(king_square, them);
            let king_orthogonal_rays = Position::orthogonal_moves(king_square, them);

            for origin in ennemy_diagonals {
                // For each diagonal attacker, generate its attack targets.
                let attack = Position::diagonal_moves(origin, non_king);
                attacked |= attack;

                // This piece is checking our king, add it to the checkers and add the
                // ray to the movable squares.
                if attack.is_set(king_square) {
                    capturable |= origin.bitboard();
                    movable |= Position::diagonal_moves(origin, position.occupancy_bitboard)
                        & king_diagonal_rays;
                }
                // This piece is accessible by our king when ignoring our own pieces, so it
                // might create a pin. This is checked by counting the number of our own pieces
                // intersected by the ray.
                else if king_diagonal_rays.is_set(origin) {
                    let ray = Position::diagonal_moves(origin, king) & king_diagonal_rays;
                    let pinned = ray & us;
                    // If the ray is blocked by more than one friendly piece, they
                    // are not pinned and we can keep going.
                    if pinned.has_more_than_one() {
                        continue;
                    }

                    // Remove the pinned piece from normal move generation
                    us ^= pinned;

                    // Then generate its moves (if any) if we're not already in check.
                    if capturable.is_empty() {
                        let movable_ray = ray ^ pinned;
                        let pinned_square = pinned.lowest_set_square_unchecked();

                        // If the pinned piece is a corresponding slider, move it along the
                        // ray and generate a capture
                        if position.pieces[pinned_square as usize]
                            .unwrap_unchecked()
                            .is_diagonal_slider()
                        {
                            moves.extend(
                                movable_ray.map(|t| LegalMove::new_quiet(pinned_square, t)),
                            );
                            moves.push_unchecked(LegalMove::new_capture(pinned_square, origin))
                        }
                        // If the pinned piece is a pawn, it can only capture the piece directly
                        // or capture en passant. Note that captures can be promotions.
                        else if position.pieces[pinned_square as usize] == Some(PieceKind::Pawn) {
                            if ((pinned & !File::H.bitboard()) + pawn_east_attack).is_set(origin)
                                || ((pinned & !File::A.bitboard()) + pawn_west_attack)
                                    .is_set(origin)
                            {
                                // Promotion capture
                                if pinned.intersects(promotion_rank) {
                                    moves.extend(LegalMove::new_promotion_capture(
                                        pinned_square,
                                        origin,
                                    ))
                                } else {
                                    moves.push_unchecked(LegalMove::new_capture(
                                        pinned_square,
                                        origin,
                                    ))
                                }
                            }

                            // En passant captures.
                            // We first check if the target is on the pin ray.
                            // If it is, we then check if the pawn to be captured
                            // doesn't discover a check
                            if let Some(file) = position.en_passant_file {
                                let (target_rank, capture_rank) = if BLACK_TO_MOVE {
                                    (Rank::Three.bitboard(), Rank::Four.bitboard())
                                } else {
                                    (Rank::Six.bitboard(), Rank::Five.bitboard())
                                };
                                let captured = file.bitboard() & capture_rank;
                                let target =
                                    (file.bitboard() & target_rank).lowest_set_square_unchecked();
                                let capturers = ((captured & !File::H.bitboard()) + Delta::East)
                                    | ((captured & !File::A.bitboard()) + Delta::West);

                                if movable_ray.is_set(target)
                                    && capturers.is_set(pinned_square)
                                    && !(Position::orthogonal_moves(
                                        king_square,
                                        position.occupancy_bitboard ^ captured ^ pinned,
                                    ) & capture_rank)
                                        .intersects(ennemy_orthogonals)
                                {
                                    moves.push_unchecked(LegalMove::new_en_passant(origin, target))
                                }
                            }
                        }
                    }
                }
            }

            // Orthogonal attacks
            for origin in ennemy_orthogonals {
                let attack = Position::orthogonal_moves(origin, non_king);
                attacked |= attack;

                // This piece is checking our king, add it to the checkers and add the
                // ray to the movable squares.
                if attack.is_set(king_square) {
                    capturable |= origin.bitboard();
                    movable |= king_orthogonal_rays
                        & Position::orthogonal_moves(origin, position.occupancy_bitboard);
                }
                // This piece is accessible by our king when ignoring our own pieces, so it
                // might create a pin. This is checked by counting the number of our own pieces
                // intersected by the ray.
                else if king_orthogonal_rays.is_set(origin) {
                    let ray = Position::orthogonal_moves(origin, king) & king_orthogonal_rays;
                    let pinned = ray & us;
                    if pinned.has_more_than_one() {
                        continue;
                    }

                    // Remove the pinned piece from normal move generation
                    us ^= pinned;

                    // Then generate its moves (if any) if we're not already in check.
                    if capturable.is_empty() {
                        let movable_ray = ray ^ pinned;
                        let pinned_square = pinned.lowest_set_square_unchecked();
                        // If the pinned piece is a corresponding slider, move it along the
                        // ray and generate a capture
                        if position.pieces[pinned_square as usize]
                            .unwrap_unchecked()
                            .is_orthogonal_slider()
                        {
                            moves.extend(
                                movable_ray.map(|t| LegalMove::new_quiet(pinned_square, t)),
                            );
                            moves.push_unchecked(LegalMove::new_capture(pinned_square, origin))
                        }
                        // If the pinned piece is a pawn, it can only push or double push
                        // if its on its original square.
                        else if position.pieces[pinned_square as usize] == Some(PieceKind::Pawn) {
                            let single_push = pinned + pawn_push;
                            if let Some(target) = (single_push & movable_ray).next() {
                                moves.push(LegalMove::new_quiet(pinned_square, target));
                                if let Some(target) =
                                    (((single_push & double_push_rank) + pawn_push) & movable_ray)
                                        .lowest_set_square()
                                {
                                    moves.push_unchecked(LegalMove::new_double_push(
                                        pinned_square,
                                        target,
                                    ))
                                }
                            }
                        }
                    }
                }
            }

            // Decide what to do based on the number of checkers.
            // If more than one checker, no moves other than the king's are legal.
            // Otherwise, we generate moves as we generally do.
            let checkers_count = capturable.cardinality();
            if checkers_count != 0 {
                // Clear pinned piece moves that might have been generated
                // before going forward
                moves.clear()
            } else {
                // If no checker: generate castling moves and restore capturable and movable masks
                // to the opponent and empty squares respectively.
                capturable = them;
                movable = !position.occupancy_bitboard;

                if position.queenside_castle_allowed::<BLACK_TO_MOVE>(attacked) {
                    moves.push_unchecked(LegalMove::new_queenside_castle::<BLACK_TO_MOVE>())
                }
                if position.kingside_castle_allowed::<BLACK_TO_MOVE>(attacked) {
                    moves.push_unchecked(LegalMove::new_kingside_castle::<BLACK_TO_MOVE>())
                }
            }

            // We generate moves for all pieces only if we're not in double check
            if checkers_count < 2 {
                // Pawn moves
                let pawns = position.piece_bitboards[PieceKind::Pawn as usize] & us;
                let promoting_pawns = pawns & promotion_rank;
                let pawns = pawns ^ promoting_pawns;

                let single_push_targets = (pawns + pawn_push) & !position.occupancy_bitboard;
                let single_push_origins = (single_push_targets & movable) - pawn_push;
                moves.extend(
                    single_push_origins
                        .zip(single_push_targets & movable)
                        .map(|(o, t)| LegalMove::new_quiet(o, t)),
                );
                let double_push_targets =
                    ((single_push_targets & double_push_rank) + pawn_push) & movable;
                let double_push_origins = double_push_targets - pawn_push - pawn_push;
                moves.extend(
                    double_push_origins
                        .zip(double_push_targets)
                        .map(|(o, t)| LegalMove::new_double_push(o, t)),
                );

                let east_captures_targets =
                    ((pawns & !File::H.bitboard()) + pawn_east_attack) & capturable;
                let east_captures_origins = east_captures_targets - pawn_east_attack;
                moves.extend(
                    east_captures_origins
                        .zip(east_captures_targets)
                        .map(|(o, t)| LegalMove::new_capture(o, t)),
                );
                let west_captures_targets =
                    ((pawns & !File::A.bitboard()) + pawn_west_attack) & capturable;
                let west_captures_origins = west_captures_targets - pawn_west_attack;
                moves.extend(
                    west_captures_origins
                        .zip(west_captures_targets)
                        .map(|(o, t)| LegalMove::new_capture(o, t)),
                );

                let promoting_push_targets = (promoting_pawns + pawn_push) & movable;
                let promoting_push_origins = promoting_push_targets - pawn_push;
                for (origin, target) in promoting_push_origins.zip(promoting_push_targets) {
                    moves.extend(LegalMove::new_promotion(origin, target))
                }
                let promoting_east_captures_targets =
                    ((promoting_pawns & !File::H.bitboard()) + pawn_east_attack) & capturable;
                let promoting_east_captures_origins =
                    promoting_east_captures_targets - pawn_east_attack;
                for (origin, target) in
                    promoting_east_captures_origins.zip(promoting_east_captures_targets)
                {
                    moves.extend(LegalMove::new_promotion_capture(origin, target))
                }
                let promoting_west_captures_targets =
                    ((promoting_pawns & !File::A.bitboard()) + pawn_west_attack) & capturable;
                let promoting_west_captures_origins =
                    promoting_west_captures_targets - pawn_west_attack;
                for (origin, target) in
                    promoting_west_captures_origins.zip(promoting_west_captures_targets)
                {
                    moves.extend(LegalMove::new_promotion_capture(origin, target))
                }

                // En passant is a bit tricky as it can leave the king in check.
                // Those moves are rare enough that we can check carefully for illegal
                // en passant capture without caring too much about the cost.
                if let Some(file) = position.en_passant_file {
                    let (target_rank, capture_rank) = if BLACK_TO_MOVE {
                        (Rank::Three.bitboard(), Rank::Four.bitboard())
                    } else {
                        (Rank::Six.bitboard(), Rank::Five.bitboard())
                    };
                    let captured = file.bitboard() & capture_rank;
                    let target = (file.bitboard() & target_rank).lowest_set_square_unchecked();

                    if captured.intersects(capturable) || movable.is_set(target) {
                        let east_attacker =
                            ((captured & !File::H.bitboard()) + Delta::East) & pawns;
                        let west_attacker =
                            ((captured & !File::A.bitboard()) + Delta::West) & pawns;

                        // Check if the king could be attacked if the attacked and attacker
                        // left the board
                        if !(Position::orthogonal_moves(
                            king_square,
                            position.occupancy_bitboard & !captured & !east_attacker,
                        ) & capture_rank)
                            .intersects(ennemy_orthogonals)
                        {
                            if let Some(origin) = east_attacker.lowest_set_square() {
                                moves.push_unchecked(LegalMove::new_en_passant(origin, target))
                            }
                        }
                        // Same for west attacks
                        if !(Position::orthogonal_moves(
                            king_square,
                            position.occupancy_bitboard & !captured & !west_attacker,
                        ) & capture_rank)
                            .intersects(ennemy_orthogonals)
                        {
                            if let Some(origin) = west_attacker.lowest_set_square() {
                                moves.push_unchecked(LegalMove::new_en_passant(origin, target))
                            }
                        }
                    }
                }

                // Knight moves
                let knights = position.piece_bitboards[PieceKind::Knight as usize] & us;
                for origin in knights {
                    let knight_moves = Position::knight_moves(origin);
                    moves.extend((knight_moves & movable).map(|t| LegalMove::new_quiet(origin, t)));
                    moves.extend(
                        (knight_moves & capturable).map(|t| LegalMove::new_capture(origin, t)),
                    );
                }

                // Sliding pieces
                let diagonal_sliders = (position.piece_bitboards[PieceKind::Bishop as usize]
                    | position.piece_bitboards[PieceKind::Queen as usize])
                    & us;
                for origin in diagonal_sliders {
                    let diagonal_moves =
                        Position::diagonal_moves(origin, position.occupancy_bitboard);
                    moves.extend(
                        (diagonal_moves & movable).map(|t| LegalMove::new_quiet(origin, t)),
                    );
                    moves.extend(
                        (diagonal_moves & capturable).map(|t| LegalMove::new_capture(origin, t)),
                    );
                }

                let orthogonal_sliders = (position.piece_bitboards[PieceKind::Rook as usize]
                    | position.piece_bitboards[PieceKind::Queen as usize])
                    & us;
                for origin in orthogonal_sliders {
                    let orthogonal_moves =
                        Position::orthogonal_moves(origin, position.occupancy_bitboard);
                    moves.extend(
                        (orthogonal_moves & movable).map(|t| LegalMove::new_quiet(origin, t)),
                    );
                    moves.extend(
                        (orthogonal_moves & capturable).map(|t| LegalMove::new_capture(origin, t)),
                    );
                }
            }

            // We always generate king moves.
            let king_moves = Position::king_moves(king_square) & !attacked;
            moves.extend(
                (king_moves & !position.occupancy_bitboard)
                    .map(|t| LegalMove::new_quiet(king_square, t)),
            );
            moves.extend((king_moves & them).map(|t| LegalMove::new_capture(king_square, t)));

            moves
        }

        unsafe {
            if self.black_to_move {
                moves_generic::<true>(self)
            } else {
                moves_generic::<false>(self)
            }
        }
    }

    /// Returns knight moves from an origin square.
    #[inline(always)]
    fn knight_moves(origin: Square) -> Bitboard {
        KNIGHT_MOVES[origin as usize]
    }

    /// Returns king moves from an origin square.
    #[inline(always)]
    fn king_moves(origin: Square) -> Bitboard {
        KING_MOVES[origin as usize]
    }

    /// Returns diagonal slider moves from an origin square and given blockers.
    #[inline(always)]
    fn diagonal_moves(origin: Square, blockers: Bitboard) -> Bitboard {
        SLIDERS_TABLE.1[origin as usize].get(blockers)
    }
    /// Returns orthogonal slider moves from an origin square and given blockers.
    #[inline(always)]
    fn orthogonal_moves(origin: Square, blockers: Bitboard) -> Bitboard {
        SLIDERS_TABLE.1[origin as usize + 64].get(blockers)
    }

    /// Checks if the side can castle queenside.
    #[inline(always)]
    fn queenside_castle_allowed<const BLACK_TO_MOVE: bool>(&self, attacked: Bitboard) -> bool {
        if BLACK_TO_MOVE {
            self.castling_rights & 0b0010 != 0
                && !self
                    .occupancy_bitboard
                    .intersects(Bitboard(0xe00000000000000))
                && !attacked.intersects(Bitboard(0xc00000000000000))
        } else {
            self.castling_rights & 0b1000 != 0
                && !self.occupancy_bitboard.intersects(Bitboard(0xe))
                && !attacked.intersects(Bitboard(0xc))
        }
    }
    /// Checks if the side can castle kingside.
    #[inline(always)]
    fn kingside_castle_allowed<const BLACK_TO_MOVE: bool>(&self, attacked: Bitboard) -> bool {
        if BLACK_TO_MOVE {
            self.castling_rights & 0b0001 != 0
                && !self
                    .occupancy_bitboard
                    .intersects(Bitboard(0x6000000000000000))
                && !attacked.intersects(Bitboard(0x6000000000000000))
        } else {
            self.castling_rights & 0b0100 != 0
                && !self.occupancy_bitboard.intersects(Bitboard(0x60))
                && !attacked.intersects(Bitboard(0x60))
        }
    }

    /// Returns the Zobrist hash of the position.
    #[inline(always)]
    pub fn zobrist_hash(&self) -> u64 {
        self.hash
    }

    // We need :
    // - one number from piece on each square (64 * 12)
    // - one number for side to move
    // - four numbers for castling rights
    // - eight numbers for en passant file

    // We use overlapping keys to make it efficiently cachable.
    // Accesses are byte aligned, making it so that we only need 784 bytes instead of
    // 3124 bytes for aligned access.
    #[inline(always)]
    const fn piece_hash<const BLACK_PIECE: bool>(kind: PieceKind, square: Square) -> u64 {
        const WHITE_PIECES_HASH: *const u8 = Position::ZOBRIST_KEYS.as_ptr().cast();
        const BLACK_PIECES_HASH: *const u8 = unsafe {
            Position::ZOBRIST_KEYS
                .as_ptr()
                .cast::<u8>()
                .offset((64 * 6) as isize)
        };
        unsafe {
            let piece_offset = kind as isize * square as isize;
            if BLACK_PIECE {
                BLACK_PIECES_HASH
                    .offset(piece_offset)
                    .cast::<u64>()
                    .read_unaligned()
            } else {
                WHITE_PIECES_HASH
                    .offset(piece_offset)
                    .cast::<u64>()
                    .read_unaligned()
            }
        }
    }
    #[inline(always)]
    const fn side_to_move_hash() -> u64 {
        const SIDE_TO_MOVE_HASH: *const u64 = unsafe {
            Position::ZOBRIST_KEYS
                .as_ptr()
                .cast::<u8>()
                .offset((64 * 12) as isize)
                .cast()
        };
        unsafe { SIDE_TO_MOVE_HASH.read_unaligned() }
    }
    #[inline(always)]
    const fn queenside_right_hash<const BLACK: bool>() -> u64 {
        const QUEENSIDE_RIGHT_WHITE_HASH: *const u64 = unsafe {
            Position::ZOBRIST_KEYS
                .as_ptr()
                .cast::<u8>()
                .offset((64 * 12 + 1) as isize)
                .cast()
        };
        const QUEENSIDE_RIGHT_BLACK_HASH: *const u64 = unsafe {
            Position::ZOBRIST_KEYS
                .as_ptr()
                .cast::<u8>()
                .offset((64 * 12 + 3) as isize)
                .cast()
        };
        unsafe {
            if BLACK {
                QUEENSIDE_RIGHT_BLACK_HASH.read_unaligned()
            } else {
                QUEENSIDE_RIGHT_WHITE_HASH.read_unaligned()
            }
        }
    }
    #[inline(always)]
    const fn kingside_right_hash<const BLACK: bool>() -> u64 {
        const KINGSIDE_RIGHT_WHITE_HASH: *const u64 = unsafe {
            Position::ZOBRIST_KEYS
                .as_ptr()
                .cast::<u8>()
                .offset((64 * 12 + 2) as isize)
                .cast()
        };
        const KINGSIDE_RIGHT_BLACK_HASH: *const u64 = unsafe {
            Position::ZOBRIST_KEYS
                .as_ptr()
                .cast::<u8>()
                .offset((64 * 12 + 4) as isize)
                .cast()
        };
        unsafe {
            if BLACK {
                KINGSIDE_RIGHT_BLACK_HASH.read_unaligned()
            } else {
                KINGSIDE_RIGHT_WHITE_HASH.read_unaligned()
            }
        }
    }
    #[inline(always)]
    const fn en_passant_file_hash(file: File) -> u64 {
        const EN_PASSANT_FILE_HASH: *const u8 = unsafe {
            Position::ZOBRIST_KEYS
                .as_ptr()
                .cast::<u8>()
                .offset((64 * 12 + 5) as isize)
                .cast()
        };
        unsafe {
            EN_PASSANT_FILE_HASH
                .offset(file as isize)
                .cast::<u64>()
                .read_unaligned()
        }
    }

    const ZOBRIST_KEYS: [u64; 196] = {
        let mut result = [0; 196];

        let mut i = 0;
        while i < 196 {
            result[i] = const_random::const_random!(u64);
            i += 1
        }

        result
    };
}
impl std::hash::Hash for Position {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.hash.hash(state)
    }
}
impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, square) in Square::squares_fen_iter().enumerate() {
            if i % 8 == 0 && i != 0 {
                match i / 8 {
                    3 => writeln!(
                        f,
                        "side to move: {}",
                        if self.black_to_move { "black" } else { "white" }
                    ),
                    4 => writeln!(f, "reversible moves: {}", self.reversible_moves),
                    5 => writeln!(
                        f,
                        "en passant: {}",
                        if let Some(file) = self.en_passant_file {
                            file.to_string()
                        } else {
                            "-".to_string()
                        }
                    ),
                    6 => writeln!(
                        f,
                        "castling rights: {}{}{}{}{}",
                        if self.castling_rights & 0b0100 != 0 {
                            "K"
                        } else {
                            ""
                        },
                        if self.castling_rights & 0b1000 != 0 {
                            "Q"
                        } else {
                            ""
                        },
                        if self.castling_rights & 0b0001 != 0 {
                            "k"
                        } else {
                            ""
                        },
                        if self.castling_rights & 0b0010 != 0 {
                            "q"
                        } else {
                            ""
                        },
                        if self.castling_rights == 0 { "-" } else { "" }
                    ),
                    7 => writeln!(f, "hash: {:#0x}", self.hash),
                    _ => writeln!(f),
                }?
            }
            write!(
                f,
                "{} ",
                match self.piece_on(square) {
                    None => ".".to_string(),
                    Some((kind, black)) =>
                        if black {
                            kind.to_string()
                        } else {
                            kind.to_string().to_uppercase()
                        },
                }
            )?
        }
        Ok(())
    }
}
