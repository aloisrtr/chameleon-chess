//! Main API to represent and interact with a chess position.
//!
//! This includes making, unmaking and generating moves, defining positions from
//! FEN strings, etc.
use std::hint::unreachable_unchecked;
use thiserror::Error;

use crate::board::zobrist;

use super::{
    action::{Action, LegalAction},
    bitboard::Bitboard,
    castling_rights::CastlingRights,
    colour::Colour,
    history::HistoryEntry,
    lookup_tables::*,
    piece::PieceKind,
    square::{Delta, File, Rank, Square},
};

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
// TODO: More precise errors
pub struct IllegalMoveError;

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Error)]
// TODO: Better FEN parsing error reports.
/// FEN parsing errors.
pub enum FenError {
    #[error("Unexpected character at index {index}: {val}")]
    UnexpectedToken { index: usize, val: char },
    #[error("FEN string missing the {0} section")]
    Incomplete(&'static str),
    #[error("Found a non-ASCII character")]
    NonAscii,
    #[error("Failed to parse")]
    ParseError,
    #[error("Piece section only defines {0} squares out of 8")]
    IncompletePieceSection(u8),
    #[error("The piece section defines too many squares")]
    TooManySquares,
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
    side_to_move: Colour,
    castling_rights: CastlingRights,
    reversible_moves: u8,
    en_passant_file: Option<File>,
    history: Vec<HistoryEntry>,
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

            side_to_move: Colour::White,
            castling_rights: CastlingRights::none(),
            reversible_moves: 0,
            en_passant_file: None,
            history: Vec::new(),
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
        let pieces = sections.first().ok_or(FenError::Incomplete("pieces"))?;
        let mut squares = Square::squares_fen_iter();
        for c in pieces.chars() {
            let black = c.is_ascii_lowercase();
            unsafe {
                match c.to_ascii_lowercase() {
                    'p' => position.add_piece_unchecked(
                        squares.next().ok_or(FenError::TooManySquares)?,
                        PieceKind::Pawn,
                        black,
                    ),
                    'n' => position.add_piece_unchecked(
                        squares.next().ok_or(FenError::TooManySquares)?,
                        PieceKind::Knight,
                        black,
                    ),
                    'b' => position.add_piece_unchecked(
                        squares.next().ok_or(FenError::TooManySquares)?,
                        PieceKind::Bishop,
                        black,
                    ),
                    'r' => position.add_piece_unchecked(
                        squares.next().ok_or(FenError::TooManySquares)?,
                        PieceKind::Rook,
                        black,
                    ),
                    'q' => position.add_piece_unchecked(
                        squares.next().ok_or(FenError::TooManySquares)?,
                        PieceKind::Queen,
                        black,
                    ),
                    'k' => position.add_piece_unchecked(
                        squares.next().ok_or(FenError::TooManySquares)?,
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

        position.side_to_move = match *sections
            .get(1)
            .ok_or(FenError::Incomplete("Side to move"))?
        {
            "w" => Colour::White,
            "b" => {
                position.hash ^= zobrist::side_to_move_hash();
                Colour::Black
            }
            _ => return Err(FenError::UnexpectedToken { index: 0, val: '0' }),
        };

        position.castling_rights = sections
            .get(2)
            .ok_or(FenError::Incomplete("Castling rights"))?
            .parse()
            .map_err(|_| FenError::ParseError)?;

        position.en_passant_file =
            match *sections.get(3).ok_or(FenError::Incomplete("En passant"))? {
                "-" => None,
                s => {
                    let file = s
                        .parse::<Square>()
                        .map_err(|_| FenError::ParseError)?
                        .file();
                    position.hash ^= zobrist::en_passant_file_hash(file);
                    Some(file)
                }
            };

        position.reversible_moves = sections.get(4).unwrap_or(&"0").parse().unwrap();

        Ok(position)
    }

    /// Returns a FEN string describing the position.
    pub fn fen(&self) -> String {
        let mut pieces = String::new();

        // Pieces
        let mut skip = 0;
        let mut line_length = 0;
        for sq in Square::squares_fen_iter() {
            if let Some((piece, colour)) = self.piece_on(sq) {
                if skip != 0 {
                    pieces.push(char::from_digit(skip, 10).unwrap());
                    skip = 0
                }
                let mut p = match piece {
                    PieceKind::Pawn => 'p',
                    PieceKind::Knight => 'n',
                    PieceKind::Bishop => 'b',
                    PieceKind::Rook => 'r',
                    PieceKind::Queen => 'q',
                    PieceKind::King => 'k',
                };
                if colour == Colour::White {
                    p = p.to_ascii_uppercase();
                }

                pieces.push(p)
            } else {
                skip += 1
            }

            line_length = (line_length + 1) % 8;
            if line_length == 0 {
                if skip != 0 {
                    pieces.push(char::from_digit(skip, 10).unwrap());
                    skip = 0;
                }
                if sq.rank() != Rank::One {
                    pieces.push('/');
                }
            }
        }

        format!(
            "{pieces} {} {} {} {} {}",
            if self.side_to_move.is_black() {
                'b'
            } else {
                'w'
            },
            self.castling_rights,
            if let Some(ep) = self.en_passant_file {
                Square::new(
                    ep,
                    if self.side_to_move.is_white() {
                        Rank::Six
                    } else {
                        Rank::Three
                    },
                )
                .to_string()
            } else {
                String::from("-")
            },
            self.reversible_moves,
            (self.history.len() + 1) / 2
        )
    }

    /// Adds a piece on the board on the given square.
    /// # Safety
    /// Placing a piece on an occupied square will result in undefined behavior.
    pub unsafe fn add_piece_unchecked(&mut self, on: Square, kind: PieceKind, black: bool) {
        let bb = on.bitboard();
        self.piece_bitboards[kind as usize] |= bb;
        self.color_bitboards[black as usize] |= bb;
        self.occupancy_bitboard |= bb;
        self.pieces[on as usize] = Some(kind);

        self.hash ^= if black {
            zobrist::piece_hash::<true>(kind, on)
        } else {
            zobrist::piece_hash::<false>(kind, on)
        }
    }

    /// Returns the piece kind and color sitting on a given square if any.
    pub fn piece_on(&self, square: Square) -> Option<(PieceKind, Colour)> {
        self.pieces[square as usize].map(|kind| {
            (
                kind,
                if self.color_bitboards[1].is_set(square) {
                    Colour::Black
                } else {
                    Colour::White
                },
            )
        })
    }

    /// Makes a move on the board, modifying the position.
    /// # Errors
    /// This function returns an error if the move is illegal.
    pub fn make(
        &mut self,
        Action {
            origin,
            target,
            promotion,
        }: Action,
    ) -> Result<(), IllegalMoveError> {
        if let Some(&mv) = self.actions().0.iter().find(|mv| {
            mv.origin() == origin && mv.target() == target && mv.is_promotion() == promotion
        }) {
            self.make_legal(mv);
            Ok(())
        } else {
            Err(IllegalMoveError)
        }
    }

    /// Makes a move on the board, modifying the position.
    #[inline]
    pub fn make_legal(&mut self, mv: LegalAction) {
        #[inline(always)]
        unsafe fn make_unchecked_generic<const BLACK_TO_MOVE: bool>(
            position: &mut Position,
            mv: LegalAction,
        ) {
            let origin = mv.origin();
            let target = mv.target();
            let move_bitboard = origin.bitboard() | target.bitboard();
            let Some(mut moving_kind) = position.pieces.get_unchecked(origin as usize) else {
                unreachable_unchecked()
            };

            let us_index = BLACK_TO_MOVE as usize;
            let them_index = !BLACK_TO_MOVE as usize;

            position.history.push(HistoryEntry {
                played: mv,
                captured: *position.pieces.get_unchecked(target as usize),
                castling_rights: position.castling_rights,
                reversible_moves: position.reversible_moves,
                en_passant_file: position.en_passant_file,
                hash: position.hash,
            });

            // Reset en passant file if any
            if let Some(en_passant_file) = position.en_passant_file.take() {
                position.hash ^= zobrist::en_passant_file_hash(en_passant_file)
            }

            // Modify castling rights if needed
            // TODO: update hash
            position.hash ^= position.castling_rights.zobrist_hash();
            for modified in move_bitboard & Bitboard(0x9100000000000091) {
                match modified {
                    Square::E1 => position.castling_rights.disallow(Colour::White),
                    Square::A1 => position
                        .castling_rights
                        .disallow_queenside_castle(Colour::White),
                    Square::H1 => position
                        .castling_rights
                        .disallow_kingside_castle(Colour::White),
                    Square::E8 => position.castling_rights.disallow(Colour::Black),
                    Square::A8 => position
                        .castling_rights
                        .disallow_queenside_castle(Colour::Black),
                    Square::H8 => position
                        .castling_rights
                        .disallow_kingside_castle(Colour::Black),
                    _ => unreachable_unchecked(),
                }
            }
            position.hash ^= position.castling_rights.zobrist_hash();

            // Take care of move kind specifics
            if let Some(to) = mv.is_promotion() {
                *position
                    .piece_bitboards
                    .get_unchecked_mut(PieceKind::Pawn as usize) ^= origin.bitboard();
                *position.piece_bitboards.get_unchecked_mut(to as usize) ^= origin.bitboard();
                *position.pieces.get_unchecked_mut(origin as usize) = Some(to);
                position.hash ^= zobrist::piece_hash::<BLACK_TO_MOVE>(moving_kind, origin);
                position.hash ^= zobrist::piece_hash::<BLACK_TO_MOVE>(to, origin);
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
                        position.hash ^= zobrist::piece_hash::<false>(captured, target);
                    } else {
                        position.hash ^= zobrist::piece_hash::<true>(captured, target);
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
                    position.hash ^= zobrist::piece_hash::<false>(captured, target);
                } else {
                    position.hash ^= zobrist::piece_hash::<true>(captured, target);
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
                position.hash ^= zobrist::piece_hash::<BLACK_TO_MOVE>(PieceKind::Rook, rook_origin);
                position.hash ^= zobrist::piece_hash::<BLACK_TO_MOVE>(PieceKind::Rook, rook_target);
                position.reversible_moves = 0
            } else if mv.special_0_is_set() {
                position.en_passant_file = Some(origin.file());
                position.hash ^= zobrist::en_passant_file_hash(origin.file());
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
            position.hash ^= zobrist::piece_hash::<BLACK_TO_MOVE>(moving_kind, origin);
            position.hash ^= zobrist::piece_hash::<BLACK_TO_MOVE>(moving_kind, target);

            position.side_to_move.invert();
            position.hash ^= zobrist::side_to_move_hash();
        }

        unsafe {
            if self.side_to_move == Colour::Black {
                make_unchecked_generic::<true>(self, mv);
            } else {
                make_unchecked_generic::<false>(self, mv);
            }
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
            position.side_to_move = if BLACK_TO_MOVE {
                Colour::Black
            } else {
                Colour::White
            };
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
                if self.side_to_move == Colour::Black {
                    unmake_generic::<false>(self, history_entry)
                } else {
                    unmake_generic::<true>(self, history_entry)
                }
            }
        }
    }

    /// Generates a list of legal moves in the current position.
    ///
    /// If this function returns an empty list, the side to move is in stalemate or checkmate.
    /// An additional flag is returned for this situation: if `true`, the side to move
    /// is in check.
    pub fn actions(&self) -> (heapless::Vec<LegalAction, 256>, bool) {
        #[inline(always)]
        unsafe fn moves_generic<const BLACK_TO_MOVE: bool>(
            position: &Position,
        ) -> (heapless::Vec<LegalAction, 256>, bool) {
            let mut moves = heapless::Vec::new();

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
                attacked |= knight_moves(origin)
            }

            // If any of those attacked squares intersects with our king, we find the checkers
            // and add them to the `capturable` set.
            if attacked.intersects(king) {
                capturable |= knight_moves(king_square) & ennemy_knights;
                capturable |= (((king & !File::H.bitboard()) + pawn_east_attack)
                    | ((king & !File::A.bitboard()) + pawn_west_attack))
                    & ennemy_pawns;
            }

            // The enemy king cannot check us legally,
            // but we still need to compute the squares it attacks.
            attacked |= king_moves(
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

            let king_diagonal_rays = diagonal_moves(king_square, them);
            let king_orthogonal_rays = orthogonal_moves(king_square, them);

            for origin in ennemy_diagonals {
                // For each diagonal attacker, generate its attack targets.
                let attack = diagonal_moves(origin, non_king);
                attacked |= attack;

                // This piece is checking our king, add it to the checkers and add the
                // ray to the movable squares.
                if attack.is_set(king_square) {
                    capturable |= origin.bitboard();
                    movable |=
                        diagonal_moves(origin, position.occupancy_bitboard) & king_diagonal_rays;
                }
                // This piece is accessible by our king when ignoring our own pieces, so it
                // might create a pin. This is checked by counting the number of our own pieces
                // intersected by the ray.
                else if king_diagonal_rays.is_set(origin) {
                    let ray = diagonal_moves(origin, king) & king_diagonal_rays;
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
                            for m in movable_ray.map(|t| LegalAction::new_quiet(pinned_square, t)) {
                                moves.push_unchecked(m)
                            }
                            moves.push_unchecked(LegalAction::new_capture(pinned_square, origin))
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
                                    for m in
                                        LegalAction::new_promotion_capture(pinned_square, origin)
                                    {
                                        moves.push_unchecked(m)
                                    }
                                } else {
                                    moves.push_unchecked(LegalAction::new_capture(
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

                                if movable_ray.is_set(target) && capturers.is_set(pinned_square) {
                                    moves
                                        .push_unchecked(LegalAction::new_en_passant(origin, target))
                                }
                            }
                        }
                    }
                }
            }

            // Orthogonal attacks
            for origin in ennemy_orthogonals {
                let attack = orthogonal_moves(origin, non_king);
                attacked |= attack;

                // This piece is checking our king, add it to the checkers and add the
                // ray to the movable squares.
                if attack.is_set(king_square) {
                    capturable |= origin.bitboard();
                    movable |= king_orthogonal_rays
                        & orthogonal_moves(origin, position.occupancy_bitboard);
                }
                // This piece is accessible by our king when ignoring our own pieces, so it
                // might create a pin. This is checked by counting the number of our own pieces
                // intersected by the ray.
                else if king_orthogonal_rays.is_set(origin) {
                    let ray = orthogonal_moves(origin, king) & king_orthogonal_rays;
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
                            for m in movable_ray.map(|t| LegalAction::new_quiet(pinned_square, t)) {
                                moves.push_unchecked(m)
                            }
                            moves.push_unchecked(LegalAction::new_capture(pinned_square, origin))
                        }
                        // If the pinned piece is a pawn, it can only push or double push
                        // if its on its original square.
                        else if position.pieces[pinned_square as usize] == Some(PieceKind::Pawn) {
                            let single_push = pinned + pawn_push;
                            if let Some(target) = (single_push & movable_ray).next() {
                                moves.push_unchecked(LegalAction::new_quiet(pinned_square, target));
                                if let Some(target) =
                                    (((single_push & double_push_rank) + pawn_push) & movable_ray)
                                        .lowest_set_square()
                                {
                                    moves.push_unchecked(LegalAction::new_double_push(
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
                    moves.push_unchecked(LegalAction::new_queenside_castle::<BLACK_TO_MOVE>())
                }
                if position.kingside_castle_allowed::<BLACK_TO_MOVE>(attacked) {
                    moves.push_unchecked(LegalAction::new_kingside_castle::<BLACK_TO_MOVE>())
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
                for m in single_push_origins
                    .zip(single_push_targets & movable)
                    .map(|(o, t)| LegalAction::new_quiet(o, t))
                {
                    moves.push_unchecked(m)
                }
                let double_push_targets =
                    ((single_push_targets & double_push_rank) + pawn_push) & movable;
                let double_push_origins = double_push_targets - pawn_push - pawn_push;
                for m in double_push_origins
                    .zip(double_push_targets)
                    .map(|(o, t)| LegalAction::new_double_push(o, t))
                {
                    moves.push_unchecked(m)
                }

                let east_captures_targets =
                    ((pawns & !File::H.bitboard()) + pawn_east_attack) & capturable;
                let east_captures_origins = east_captures_targets - pawn_east_attack;

                for m in east_captures_origins
                    .zip(east_captures_targets)
                    .map(|(o, t)| LegalAction::new_capture(o, t))
                {
                    moves.push_unchecked(m)
                }
                let west_captures_targets =
                    ((pawns & !File::A.bitboard()) + pawn_west_attack) & capturable;
                let west_captures_origins = west_captures_targets - pawn_west_attack;
                for m in west_captures_origins
                    .zip(west_captures_targets)
                    .map(|(o, t)| LegalAction::new_capture(o, t))
                {
                    moves.push_unchecked(m)
                }

                let promoting_push_targets = (promoting_pawns + pawn_push) & movable;
                let promoting_push_origins = promoting_push_targets - pawn_push;
                for (origin, target) in promoting_push_origins.zip(promoting_push_targets) {
                    for m in LegalAction::new_promotion(origin, target) {
                        moves.push_unchecked(m)
                    }
                }
                let promoting_east_captures_targets =
                    ((promoting_pawns & !File::H.bitboard()) + pawn_east_attack) & capturable;
                let promoting_east_captures_origins =
                    promoting_east_captures_targets - pawn_east_attack;
                for (origin, target) in
                    promoting_east_captures_origins.zip(promoting_east_captures_targets)
                {
                    for m in LegalAction::new_promotion_capture(origin, target) {
                        moves.push_unchecked(m)
                    }
                }
                let promoting_west_captures_targets =
                    ((promoting_pawns & !File::A.bitboard()) + pawn_west_attack) & capturable;
                let promoting_west_captures_origins =
                    promoting_west_captures_targets - pawn_west_attack;
                for (origin, target) in
                    promoting_west_captures_origins.zip(promoting_west_captures_targets)
                {
                    for m in LegalAction::new_promotion_capture(origin, target) {
                        moves.push_unchecked(m)
                    }
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
                        if !(orthogonal_moves(
                            king_square,
                            position.occupancy_bitboard & !captured & !east_attacker,
                        ) & capture_rank)
                            .intersects(ennemy_orthogonals)
                        {
                            if let Some(origin) = east_attacker.lowest_set_square() {
                                moves.push_unchecked(LegalAction::new_en_passant(origin, target))
                            }
                        }
                        // Same for west attacks
                        if !(orthogonal_moves(
                            king_square,
                            position.occupancy_bitboard & !captured & !west_attacker,
                        ) & capture_rank)
                            .intersects(ennemy_orthogonals)
                        {
                            if let Some(origin) = west_attacker.lowest_set_square() {
                                moves.push_unchecked(LegalAction::new_en_passant(origin, target))
                            }
                        }
                    }
                }

                // Knight moves
                let knights = position.piece_bitboards[PieceKind::Knight as usize] & us;
                for origin in knights {
                    let knight_moves = knight_moves(origin);
                    for m in (knight_moves & movable).map(|t| LegalAction::new_quiet(origin, t)) {
                        moves.push_unchecked(m)
                    }
                    for m in
                        (knight_moves & capturable).map(|t| LegalAction::new_capture(origin, t))
                    {
                        moves.push_unchecked(m)
                    }
                }

                // Sliding pieces
                let diagonal_sliders = (position.piece_bitboards[PieceKind::Bishop as usize]
                    | position.piece_bitboards[PieceKind::Queen as usize])
                    & us;
                for origin in diagonal_sliders {
                    let diagonal_moves = diagonal_moves(origin, position.occupancy_bitboard);
                    for m in (diagonal_moves & movable).map(|t| LegalAction::new_quiet(origin, t)) {
                        moves.push_unchecked(m)
                    }
                    for m in
                        (diagonal_moves & capturable).map(|t| LegalAction::new_capture(origin, t))
                    {
                        moves.push_unchecked(m)
                    }
                }

                let orthogonal_sliders = (position.piece_bitboards[PieceKind::Rook as usize]
                    | position.piece_bitboards[PieceKind::Queen as usize])
                    & us;
                for origin in orthogonal_sliders {
                    let orthogonal_moves = orthogonal_moves(origin, position.occupancy_bitboard);

                    for m in (orthogonal_moves & movable).map(|t| LegalAction::new_quiet(origin, t))
                    {
                        moves.push_unchecked(m)
                    }
                    for m in
                        (orthogonal_moves & capturable).map(|t| LegalAction::new_capture(origin, t))
                    {
                        moves.push_unchecked(m)
                    }
                }
            }

            // We always generate king moves.
            let king_moves = king_moves(king_square) & !attacked;
            for m in (king_moves & !position.occupancy_bitboard)
                .map(|t| LegalAction::new_quiet(king_square, t))
            {
                moves.push_unchecked(m)
            }
            for m in (king_moves & them).map(|t| LegalAction::new_capture(king_square, t)) {
                moves.push_unchecked(m)
            }

            (moves, checkers_count != 0)
        }

        unsafe {
            if self.side_to_move == Colour::Black {
                moves_generic::<true>(self)
            } else {
                moves_generic::<false>(self)
            }
        }
    }

    /// Checks if a threefold repetition occured in this game.
    pub fn threefold_repetition(&self) -> bool {
        self.history
            .iter()
            .rev()
            .take(self.reversible_moves as usize)
            .filter(|entry| entry.hash == self.hash)
            .count()
            == 2
    }

    /// Checks if this position is drawn by the fifty-move rule.
    pub fn fifty_move_draw(&self) -> bool {
        self.reversible_moves >= 100
    }

    /// Checks if the side can castle queenside.
    #[inline(always)]
    fn queenside_castle_allowed<const BLACK_TO_MOVE: bool>(&self, attacked: Bitboard) -> bool {
        if BLACK_TO_MOVE {
            self.castling_rights.queenside_castle_allowed(Colour::Black)
                && !self
                    .occupancy_bitboard
                    .intersects(Bitboard(0xe00000000000000))
                && !attacked.intersects(Bitboard(0xc00000000000000))
        } else {
            self.castling_rights.queenside_castle_allowed(Colour::White)
                && !self.occupancy_bitboard.intersects(Bitboard(0xe))
                && !attacked.intersects(Bitboard(0xc))
        }
    }
    /// Checks if the side can castle kingside.
    #[inline(always)]
    fn kingside_castle_allowed<const BLACK_TO_MOVE: bool>(&self, attacked: Bitboard) -> bool {
        if BLACK_TO_MOVE {
            self.castling_rights.kingside_castle_allowed(Colour::Black)
                && !self
                    .occupancy_bitboard
                    .intersects(Bitboard(0x6000000000000000))
                && !attacked.intersects(Bitboard(0x6000000000000000))
        } else {
            self.castling_rights.kingside_castle_allowed(Colour::White)
                && !self.occupancy_bitboard.intersects(Bitboard(0x60))
                && !attacked.intersects(Bitboard(0x60))
        }
    }

    /// Returns the Zobrist hash of the position.
    #[inline(always)]
    pub fn zobrist_hash(&self) -> u64 {
        self.hash
    }
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
                        if self.side_to_move == Colour::Black {
                            "black"
                        } else {
                            "white"
                        }
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
                    6 => writeln!(f, "castling rights: {}", self.castling_rights),
                    7 => writeln!(f, "hash: {:#0x}", self.hash),
                    _ => writeln!(f),
                }?
            }
            write!(
                f,
                "{} ",
                match self.piece_on(square) {
                    None => ".".to_string(),
                    Some((kind, color)) =>
                        if kind == PieceKind::Pawn {
                            if color == Colour::Black {
                                String::from("x")
                            } else {
                                String::from("o")
                            }
                        } else if color == Colour::Black {
                            kind.to_string()
                        } else {
                            kind.to_string().to_uppercase()
                        },
                }
            )?
        }

        writeln!(f, "\nfen: {}", self.fen())
    }
}

#[cfg(test)]
mod test {
    use crate::board::{action::Action, square::Square};

    use super::Position;

    #[test]
    fn hash_test() {
        let mut pos = Position::initial();
        let og_hash = pos.zobrist_hash();
        pos.make(Action::new(Square::E2, Square::E4)).unwrap();
        pos.unmake();
        assert_eq!(og_hash, pos.zobrist_hash())
    }
}
