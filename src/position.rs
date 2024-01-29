//! Main API to represent and interact with a chess position.
//!
//! This includes making, unmaking and generating moves, defining positions from
//! FEN strings, etc.
use std::hint::unreachable_unchecked;

use arrayvec::ArrayVec;

use crate::{
    bitboard::Bitboard,
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

/// An entry in the sliders' move lookup table.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
struct SliderTableEntry {
    magic: u64,
    blockers_mask: Bitboard,
    shift: u8,
    offset: usize,
}
impl SliderTableEntry {
    /// Given a set of blockers, returns the corresponding bitboard of reachable
    /// squares from the slider table.
    #[inline(always)]
    pub fn get(self, blockers: Bitboard) -> Bitboard {
        unsafe {
            *Position::SLIDER_MOVES.get_unchecked(
                self.offset
                    + ((blockers.0 & self.blockers_mask.0).wrapping_mul(self.magic) >> self.shift)
                        as usize,
            )
        }
    }
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
            Self::piece_hash::<true>(kind, on)
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

            let (
                pawn_push,
                pawn_east_attack,
                pawn_west_attack,
                promotion_rank,
                en_passant_rank,
                double_push_rank,
            ) = if BLACK_TO_MOVE {
                (
                    Delta::South,
                    Delta::SouthEast,
                    Delta::SouthWest,
                    Rank::Two.bitboard(),
                    Rank::Three.bitboard(),
                    Rank::Six.bitboard(),
                )
            } else {
                (
                    Delta::North,
                    Delta::NorthEast,
                    Delta::NorthWest,
                    Rank::Seven.bitboard(),
                    Rank::Six.bitboard(),
                    Rank::Three.bitboard(),
                )
            };

            let king = position.piece_bitboards[PieceKind::King as usize] & us;
            let king_square = king.lowest_set_square_unchecked();

            // Test for pins and attacks.
            // We generate moves for pinned pieces directly when detecting them. Those
            // pieces are masked from bitboards afterwards.

            // If we find a direct attack to the king, we can now ignore pinned pieces
            // since their moves are known to be illegal.

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
            for origin in ennemy_knights {
                attacked |= Position::KNIGHT_MOVES[origin as usize]
            }

            // If any of those attacked squares intersects with our king, we find the checkers
            // and add them to the `capturable` set.
            if attacked.intersects(king) {
                capturable |= Position::KNIGHT_MOVES[king_square as usize] & ennemy_knights;
                capturable |= (((king & !File::H.bitboard()) + pawn_east_attack)
                    | ((king & !File::A.bitboard()) + pawn_west_attack))
                    & ennemy_pawns;
            }

            // The enemy king cannot check us legally,
            // but we still need to compute the squares it attacks.
            let ennemy_king = (position.piece_bitboards[PieceKind::King as usize] & them)
                .lowest_set_square_unchecked();
            attacked |= Position::KING_MOVES[ennemy_king as usize];

            // We then deal with ray attacks. These can produce pins and are blockable.
            // For each sliding piece, we generate its moves and then check for two scenarios:
            // - either the piece directly attacks our king, we're in check and add the slider to the `capturable` set.
            // - or the piece can attack our king when xraying our pieces. In this case, the slider might create a pin.
            let ennemy_queens = position.piece_bitboards[PieceKind::Queen as usize] & them;
            let ennemy_bishops = position.piece_bitboards[PieceKind::Bishop as usize] & them;
            let ennemy_diagonals = ennemy_queens | ennemy_bishops;

            let king_diagonal_rays = Position::diagonal_moves(king_square, them);
            let non_king = position.occupancy_bitboard ^ king;

            for origin in ennemy_diagonals {
                let attack = Position::diagonal_moves(origin, non_king);
                attacked |= attack;

                // This piece is checking our king, add it to the checkers and add the
                // ray to the movable squares.
                if attack.intersects(king) {
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
                    if pinned.has_more_than_one() {
                        continue;
                    }
                    let ray = ray ^ pinned;
                    let pinned_square = pinned.lowest_set_square_unchecked();

                    // Remove the pinned piece from normal move generation
                    us ^= pinned;

                    // Then generate its moves (if any) if we're not already in check.
                    if capturable.is_empty() {
                        // If the pinned piece is a corresponding slider, move it along the
                        // ray and generate a capture
                        if (position.piece_bitboards[PieceKind::Bishop as usize]
                            | position.piece_bitboards[PieceKind::Queen as usize])
                            .intersects(pinned)
                        {
                            for target in ray {
                                moves.push_unchecked(LegalMove::new_quiet(pinned_square, target))
                            }
                            moves.push_unchecked(LegalMove::new_capture(pinned_square, origin))
                        }
                        // If the pinned piece is a pawn, it can only capture the piece directly
                        // or capture en passant. Note that captures can be promotions.
                        else if position.piece_bitboards[PieceKind::Pawn as usize]
                            .intersects(pinned)
                        {
                            if ((pinned & !File::H.bitboard()) + pawn_east_attack).is_set(origin)
                                || ((pinned & !File::A.bitboard()) + pawn_west_attack)
                                    .is_set(origin)
                            {
                                // Promotion capture
                                if pinned.intersects(promotion_rank) {
                                    moves
                                        .try_extend_from_slice(&LegalMove::new_promotion_capture(
                                            pinned_square,
                                            origin,
                                        ))
                                        .unwrap_unchecked();
                                } else {
                                    moves.push_unchecked(LegalMove::new_capture(
                                        pinned_square,
                                        origin,
                                    ))
                                }
                            }

                            // En passant captures are hell.
                            // We first check if the target is on the pin ray.
                            // If it is, we then check if the pawn to be captured
                            // doesn't discover a check
                            if let Some(_file) = position.en_passant_file {
                                // TODO
                            }
                        }
                    }
                }
            }

            // Repeat for orthogonal sliders
            let ennemy_rooks = position.piece_bitboards[PieceKind::Rook as usize] & them;
            let ennemy_orthogonals = ennemy_rooks | ennemy_queens;

            let king_orthogonal_rays = Position::orthogonal_moves(king_square, them);

            for origin in ennemy_orthogonals {
                let attack = Position::orthogonal_moves(origin, non_king);
                attacked |= attack;

                // This piece is checking our king, add it to the checkers and add the
                // ray to the movable squares.
                if attack.intersects(king) {
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
                    let ray = ray ^ pinned;
                    let pinned_square = pinned.lowest_set_square_unchecked();

                    // Remove the pinned piece from normal move generation
                    us ^= pinned;

                    // Then generate its moves (if any) if we're not already in check.
                    if capturable.is_empty() {
                        // If the pinned piece is a corresponding slider, move it along the
                        // ray and generate a capture
                        if (position.piece_bitboards[PieceKind::Rook as usize]
                            | position.piece_bitboards[PieceKind::Queen as usize])
                            .intersects(pinned)
                        {
                            for target in ray {
                                moves.push_unchecked(LegalMove::new_quiet(pinned_square, target))
                            }
                            moves.push_unchecked(LegalMove::new_capture(pinned_square, origin))
                        }
                        // If the pinned piece is a pawn, it can only push or double push
                        // if its on its original square.
                        else if position.piece_bitboards[PieceKind::Pawn as usize]
                            .intersects(pinned)
                        {
                            let single_push = pinned + pawn_push;
                            if let Some(target) = (single_push & ray).next() {
                                moves.push(LegalMove::new_quiet(pinned_square, target));
                                if let Some(target) =
                                    (((single_push & double_push_rank) + pawn_push) & ray)
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
            if capturable.has_at_most_one() {
                if capturable.is_empty() {
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
                } else {
                    // Otherwise, clear pinned piece moves that might have been generated
                    // before going forward
                    moves.clear()
                }

                // Pawn moves
                let pawns = position.piece_bitboards[PieceKind::Pawn as usize] & us;
                let promoting_pawns = pawns & promotion_rank;
                let pawns = pawns ^ promoting_pawns;

                let single_push = (pawns + pawn_push) & !position.occupancy_bitboard;
                let double_push = ((single_push & double_push_rank) + pawn_push) & movable;
                for target in double_push {
                    moves.push_unchecked(LegalMove::new_double_push(
                        target - pawn_push - pawn_push,
                        target,
                    ))
                }

                for target in single_push & movable {
                    moves.push_unchecked(LegalMove::new_quiet(target - pawn_push, target))
                }

                let east_captures = ((pawns & !File::H.bitboard()) + pawn_east_attack) & capturable;
                for target in east_captures {
                    moves.push_unchecked(LegalMove::new_capture(target - pawn_east_attack, target))
                }
                let west_captures = ((pawns & !File::A.bitboard()) + pawn_west_attack) & capturable;
                for target in west_captures {
                    moves.push_unchecked(LegalMove::new_capture(target - pawn_west_attack, target))
                }

                let promoting_push = (promoting_pawns + pawn_push) & movable;
                for target in promoting_push {
                    moves
                        .try_extend_from_slice(&LegalMove::new_promotion(
                            target - pawn_push,
                            target,
                        ))
                        .unwrap_unchecked()
                }
                let promoting_east_captures =
                    ((promoting_pawns & !File::H.bitboard()) + pawn_east_attack) & capturable;
                for target in promoting_east_captures {
                    moves
                        .try_extend_from_slice(&LegalMove::new_promotion_capture(
                            target - pawn_east_attack,
                            target,
                        ))
                        .unwrap_unchecked()
                }
                let promoting_west_captures =
                    ((promoting_pawns & !File::A.bitboard()) + pawn_west_attack) & capturable;
                for target in promoting_west_captures {
                    moves
                        .try_extend_from_slice(&LegalMove::new_promotion_capture(
                            target - pawn_west_attack,
                            target,
                        ))
                        .unwrap_unchecked()
                }

                // En passant is a bit tricky as it can leave the king in check.
                // Those moves are rare enough that we can check carefully for illegal
                // en passant capture without caring too much about the cost.
                if let Some(file) = position.en_passant_file {
                    let capture_rank = if BLACK_TO_MOVE {
                        Rank::Four.bitboard()
                    } else {
                        Rank::Five.bitboard()
                    };
                    let captured = file.bitboard() & capture_rank;
                    let target = (file.bitboard() & en_passant_rank).lowest_set_square_unchecked();

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
                            && !Position::diagonal_moves(
                                king_square,
                                position.occupancy_bitboard & !captured,
                            )
                            .intersects(ennemy_diagonals)
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
                            && !Position::diagonal_moves(
                                king_square,
                                position.occupancy_bitboard & !captured,
                            )
                            .intersects(ennemy_diagonals)
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
                    let knight_moves = Position::KNIGHT_MOVES[origin as usize];
                    for target in knight_moves & movable {
                        moves.push_unchecked(LegalMove::new_quiet(origin, target))
                    }

                    for target in knight_moves & capturable {
                        moves.push_unchecked(LegalMove::new_capture(origin, target))
                    }
                }

                // Sliding pieces
                let diagonal_sliders = (position.piece_bitboards[PieceKind::Bishop as usize]
                    | position.piece_bitboards[PieceKind::Queen as usize])
                    & us;
                for origin in diagonal_sliders {
                    let diagonal_moves =
                        Position::diagonal_moves(origin, position.occupancy_bitboard);
                    for target in diagonal_moves & movable {
                        moves.push_unchecked(LegalMove::new_quiet(origin, target))
                    }

                    for target in diagonal_moves & capturable {
                        moves.push_unchecked(LegalMove::new_capture(origin, target))
                    }
                }

                let orthogonal_sliders = (position.piece_bitboards[PieceKind::Rook as usize]
                    | position.piece_bitboards[PieceKind::Queen as usize])
                    & us;
                for origin in orthogonal_sliders {
                    let diagonal_moves =
                        Position::orthogonal_moves(origin, position.occupancy_bitboard);
                    for target in diagonal_moves & movable {
                        moves.push_unchecked(LegalMove::new_quiet(origin, target))
                    }

                    for target in diagonal_moves & capturable {
                        moves.push_unchecked(LegalMove::new_capture(origin, target))
                    }
                }
            }

            // We always generate king moves.
            let king_moves = Position::KING_MOVES[king_square as usize] & !attacked;
            for target in king_moves & !position.occupancy_bitboard {
                moves.push_unchecked(LegalMove::new_quiet(king_square, target));
            }
            for target in king_moves & them {
                moves.push_unchecked(LegalMove::new_capture(king_square, target));
            }

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

    /// Lookup for king moves from a given square.
    const KING_MOVES: [Bitboard; 64] = {
        let mut result = [Bitboard::empty(); 64];
        let mut origin = 0;
        let west = File::A.bitboard().invert();
        let east = File::H.bitboard().invert();
        while origin < 64 {
            let origin_bb = Bitboard(1 << origin);
            result[origin as usize].0 |= origin_bb.intersection(west).shift(Delta::West).0
                | origin_bb.intersection(east).shift(Delta::East).0
                | origin_bb.shift(Delta::North).0
                | origin_bb.shift(Delta::South).0
                | origin_bb.intersection(east).shift(Delta::NorthEast).0
                | origin_bb.intersection(east).shift(Delta::SouthEast).0
                | origin_bb.intersection(west).shift(Delta::NorthWest).0
                | origin_bb.intersection(west).shift(Delta::SouthWest).0;

            origin += 1;
        }
        result
    };

    /// Lookup for knight moves from a given square.
    const KNIGHT_MOVES: [Bitboard; 64] = {
        let mut result = [Bitboard::empty(); 64];
        let mut origin = 0;
        let west = File::A.bitboard().invert();
        let east = File::H.bitboard().invert();
        let two_west = File::A
            .bitboard()
            .invert()
            .intersection(File::B.bitboard().invert());
        let two_east = File::H
            .bitboard()
            .invert()
            .intersection(File::G.bitboard().invert());
        while origin < 64 {
            let origin_bb = Bitboard(1 << origin);
            result[origin as usize].0 |=
                origin_bb.intersection(east).shift(Delta::KnightNorthEast).0
                    | origin_bb.intersection(west).shift(Delta::KnightNorthWest).0
                    | origin_bb.intersection(east).shift(Delta::KnightSouthEast).0
                    | origin_bb.intersection(west).shift(Delta::KnightSouthWest).0
                    | origin_bb
                        .intersection(two_east)
                        .shift(Delta::KnightEastNorth)
                        .0
                    | origin_bb
                        .intersection(two_west)
                        .shift(Delta::KnightWestNorth)
                        .0
                    | origin_bb
                        .intersection(two_east)
                        .shift(Delta::KnightEastSouth)
                        .0
                    | origin_bb
                        .intersection(two_west)
                        .shift(Delta::KnightWestSouth)
                        .0;

            origin += 1;
        }
        result
    };

    /// Returns diagonal slider moves from an origin square and given blockers.
    #[inline(always)]
    fn diagonal_moves(origin: Square, blockers: Bitboard) -> Bitboard {
        Self::SLIDER_TABLE_ENTRIES[origin as usize].get(blockers)
    }
    /// Returns orthogonal slider moves from an origin square and given blockers.
    #[inline(always)]
    fn orthogonal_moves(origin: Square, blockers: Bitboard) -> Bitboard {
        Self::SLIDER_TABLE_ENTRIES[origin as usize + 64].get(blockers)
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

    const SLIDER_TABLE_ENTRIES: [SliderTableEntry; 128] = {
        use std::mem::MaybeUninit;
        let mut result: [MaybeUninit<SliderTableEntry>; 128] =
            unsafe { MaybeUninit::uninit().assume_init() };
        let magics: [u64; 128] = [
            293861533946085504,
            99361787782299656,
            22525712988637184,
            4613984015446213888,
            5068817994614090,
            2594359289528517184,
            106721483702305,
            81205810356633664,
            144119792358458368,
            11872053775349449216,
            13835075664652451840,
            5513685797012766784,
            2305847463640276992,
            42784772266663942,
            1153203565914767872,
            297273035764830208,
            5242226387951288624,
            797137143439885064,
            1157425108546093072,
            2324983410830872576,
            19144705070333954,
            9241562365849242112,
            1234273289829892616,
            77405623762879504,
            2310645693859631104,
            82226501491623040,
            1129267195281664,
            4648286562633666592,
            288375512231845904,
            13511906992079130,
            9692872916553040128,
            576534421785085957,
            5766863996057815300,
            112735267954098752,
            4760516118593409088,
            36592299429462528,
            577587751990591552,
            652177817391465232,
            3395850386800896,
            4614089689358532864,
            943697653966118912,
            9656847917364814336,
            10700844361299529728,
            1152921780294320640,
            1225832388660102144,
            9225907613781336128,
            49698587008839744,
            13671329744027680,
            651056638528127296,
            2816955334008835,
            2262804627720256,
            2305984898861761024,
            1176854726913,
            144150389896282368,
            2254067623727488,
            4543217220069376,
            578220254453325888,
            1300415494196822656,
            159968119631228928,
            11269994189029888,
            136381706,
            180665516544,
            576496623937978432,
            4616207218964971536,
            4647715090332655792,
            1459167654462906369,
            144125633753120832,
            2954366862241038424,
            1297063219743031300,
            72059814541525000,
            1224988994410127872,
            36036493603553664,
            6918232732809576448,
            4611827030802063360,
            9228157184475399360,
            288371182367934464,
            1153203055097825280,
            72198614994387072,
            8072983953071673600,
            18155284174225664,
            18023744383633832,
            40532671593448016,
            4683815081258012930,
            612518137700553216,
            1167576895161106688,
            292875264130569216,
            4614232487500972802,
            74386359732707393,
            180495830965321728,
            9007337767522304,
            5069306951122976,
            1153203018239312096,
            9223447907454681296,
            2306405967757349128,
            18093580529697538,
            4611826895502459136,
            27162353590083840,
            35195252129793,
            729587816870187040,
            4504149727119360,
            578714201527157760,
            432908548574284816,
            2312616172706611713,
            9241527191785701632,
            13835199067751219201,
            1170936180158824481,
            1152939097329795200,
            563224968036368,
            297801281811382280,
            144181158807109760,
            281500746579972,
            36873291884986370,
            563449318932992,
            1153062379555127680,
            2394805046872192,
            4620836738310340736,
            145522718786261248,
            360448498954436736,
            20973229532251136,
            2449963974097895936,
            71473121210498,
            2392952185831425,
            9232389142764060737,
            9226186855879034946,
            1188959098013810693,
            613334010797752337,
            72339077604839557,
            2333991061002658114,
        ];
        let blockers: [u64; 128] = [
            18049651735527936,
            70506452091904,
            275415828992,
            1075975168,
            38021120,
            8657588224,
            2216338399232,
            567382630219776,
            9024825867763712,
            18049651735527424,
            70506452221952,
            275449643008,
            9733406720,
            2216342585344,
            567382630203392,
            1134765260406784,
            4512412933816832,
            9024825867633664,
            18049651768822272,
            70515108615168,
            2491752130560,
            567383701868544,
            1134765256220672,
            2269530512441344,
            2256206450263040,
            4512412900526080,
            9024834391117824,
            18051867805491712,
            637888545440768,
            1135039602493440,
            2269529440784384,
            4539058881568768,
            1128098963916800,
            2256197927833600,
            4514594912477184,
            9592139778506752,
            19184279556981248,
            2339762086609920,
            4538784537380864,
            9077569074761728,
            562958610993152,
            1125917221986304,
            2814792987328512,
            5629586008178688,
            11259172008099840,
            22518341868716544,
            9007336962655232,
            18014673925310464,
            2216338399232,
            4432676798464,
            11064376819712,
            22137335185408,
            44272556441600,
            87995357200384,
            35253226045952,
            70506452091904,
            567382630219776,
            1134765260406784,
            2832480465846272,
            5667157807464448,
            11333774449049600,
            22526811443298304,
            9024825867763712,
            18049651735527936,
            282578800148862,
            565157600297596,
            1130315200595066,
            2260630401190006,
            4521260802379886,
            9042521604759646,
            18085043209519166,
            36170086419038334,
            282578800180736,
            565157600328704,
            1130315200625152,
            2260630401218048,
            4521260802403840,
            9042521604775424,
            18085043209518592,
            36170086419037696,
            282578808340736,
            565157608292864,
            1130315208328192,
            2260630408398848,
            4521260808540160,
            9042521608822784,
            18085043209388032,
            36170086418907136,
            282580897300736,
            565159647117824,
            1130317180306432,
            2260632246683648,
            4521262379438080,
            9042522644946944,
            18085043175964672,
            36170086385483776,
            283115671060736,
            565681586307584,
            1130822006735872,
            2261102847592448,
            4521664529305600,
            9042787892731904,
            18085034619584512,
            36170077829103616,
            420017753620736,
            699298018886144,
            1260057572672512,
            2381576680245248,
            4624614895390720,
            9110691325681664,
            18082844186263552,
            36167887395782656,
            35466950888980736,
            34905104758997504,
            34344362452452352,
            33222877839362048,
            30979908613181440,
            26493970160820224,
            17522093256097792,
            35607136465616896,
            9079539427579068672,
            8935706818303361536,
            8792156787827803136,
            8505056726876686336,
            7930856604974452736,
            6782456361169985536,
            4485655873561051136,
            9115426935197958144,
        ];

        let mut i = 0;
        let mut offset = 0;
        while i < 128 {
            let bits = blockers[i].count_ones() as u8;
            let shift = 64 - bits;
            result[i] = MaybeUninit::new(SliderTableEntry {
                magic: magics[i],
                blockers_mask: Bitboard(blockers[i]),
                shift,
                offset,
            });
            offset += 1 << bits;
            i += 1;
        }

        unsafe { std::mem::transmute(result) }
    };

    /// This constant is computed ASSUMING THAT SLIDER_TABLE_ENTRIES IS CORRECT.
    /// If this assumption doesn't hold, the program is entirely incorrect.
    const SLIDER_MOVES_SIZE: usize = 107648;
    #[allow(long_running_const_eval)]
    const SLIDER_MOVES: [Bitboard; Self::SLIDER_MOVES_SIZE] = {
        let mut result = [Bitboard::empty(); Self::SLIDER_MOVES_SIZE];

        let mut square = 0;
        let mut offset = 0;
        while square < 128 {
            let SliderTableEntry {
                magic,
                blockers_mask,
                shift,
                ..
            } = Self::SLIDER_TABLE_ENTRIES[square];

            let origin = unsafe { Square::from_index_unchecked(square as u8 % 64) };

            let mut blockers = Bitboard::empty();
            loop {
                let index =
                    offset + ((blockers.0 & blockers_mask.0).wrapping_mul(magic) >> shift) as usize;

                // Generate moves
                if result[index].is_empty() {
                    let deltas = if square < 64 {
                        [
                            Delta::NorthEast,
                            Delta::NorthWest,
                            Delta::SouthEast,
                            Delta::SouthWest,
                        ]
                    } else {
                        [Delta::North, Delta::South, Delta::East, Delta::West]
                    };

                    let mut i = 0;
                    while i < 4 {
                        let delta = deltas[i];
                        let Some(mut current_square) = origin.translate(delta) else {
                            i += 1;
                            continue;
                        };
                        'ray: loop {
                            result[index].0 |= 1 << current_square as u8;
                            if (blockers.0 & (1 << current_square as u8)) != 0 {
                                break 'ray;
                            } else if let Some(sq) = current_square.translate(delta) {
                                current_square = sq;
                            } else {
                                break 'ray;
                            }
                        }

                        i += 1
                    }
                }

                blockers.0 = blockers.0.wrapping_sub(blockers_mask.0) & blockers_mask.0;
                if blockers.is_empty() {
                    break;
                }
            }

            offset += 1 << (64 - shift);
            square += 1;
        }

        result
    };

    /// Returns the Zobrist hash of the position.
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
