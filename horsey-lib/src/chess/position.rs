//! Main API to represent and interact with a chess position.
//!
//! This includes making, unmaking and generating moves, defining positions from
//! FEN strings, etc.

use crate::brain::feature::{feature_index, piece_feature_index};
use std::hint::unreachable_unchecked;

use super::{
    action::{Action, ChessMove, SanMove, SanMoveKind, UciMove},
    bitboard::Bitboard,
    castling_rights::CastlingRights,
    colour::Colour,
    fen::Fen,
    history::HistoryEntry,
    magic_tables::*,
    piece::{Piece, PieceKind},
    square::{Delta, File, Rank, Square},
    zobrist,
};

pub type ActionList = heapless::Vec<Action, 256>;

/// Indicates that an illegal move was played.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
// TODO: More precise errors
pub struct IllegalMoveError;

/// Indicates placement errors for pieces, leading to incorrect positions.
pub enum PlaceError {
    SquareOccupied { kind: PieceKind, colour: Colour },
    TooManyKings(Colour),
}

/// Possible result of the game.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum GameResult {
    /// A side is in checkmate. The value in this variant indicates which side **is in checkmate**,
    /// not the side that won.
    Checkmate(Colour),
    /// A draw was reached. The value in this variant indicates the type of draw.
    Draw(DrawKind),
}

/// The types of checks that can be given.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum CheckKind {
    CheckMate,
    DoubleCheck,
    Check,
}

/// All possible kinds of draw.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum DrawKind {
    /// One side has no legal moves, yet is not in check.
    Stalemate,
    /// The same position was repeated three times.
    Repetition,
    /// Fifty plys have been played without any capture or pawn pushes.
    FiftyMoveRule,
    /// None of the players can force checkmate.
    InsufficientMaterial,
    /// Both players agreed to a draw.
    Agreement,
}

/// Stores attack information for a given position.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AttackInformation {
    checkers: Bitboard,
    check_rays: Bitboard,
    attacked: Bitboard,
    pinned: Bitboard,
    movable_pins: heapless::Vec<(Square, Bitboard), 8>,
}
impl AttackInformation {
    /// Returns the number of checking pieces.
    #[inline(always)]
    pub fn checkers_count(&self) -> u8 {
        self.checkers.cardinality()
    }

    /// Returns `true` if there is at least one checker. Combined with [`Position::actions`],
    /// this can be used to acertain whether the side to move is in checkmate or
    /// stalemate.
    #[inline(always)]
    pub fn in_check(&self) -> bool {
        self.checkers.is_not_empty()
    }

    /// Returns `true` if there is more than one checker.
    #[inline(always)]
    pub fn in_double_check(&self) -> bool {
        self.checkers.has_more_than_one()
    }
}

/// Represents a valid chess position and defines an API to interact with said
/// position (making, unmaking, generating moves, etc).
#[derive(PartialEq, Eq, Clone)]
pub struct Position {
    // 8x8 array to find which piece sits on which square.
    pieces: [Option<PieceKind>; 64],
    // Bitboards are indexed by piece kind + 2 and color.
    bitboards: [Bitboard; 8],

    // Metadata
    side_to_move: Colour,
    castling_rights: CastlingRights,
    reversible_moves: u8,
    en_passant_file: Option<File>,
    history: Vec<HistoryEntry>,
    hash: u64,

    // NNUE
    added_features: Vec<u16>,
    removed_features: Vec<u16>,
    should_refresh: bool,
}
impl Default for Position {
    /// A position with no pieces.
    fn default() -> Self {
        Self {
            pieces: [None; 64],
            bitboards: [Bitboard::empty(); 8],

            side_to_move: Colour::White,
            castling_rights: CastlingRights::none(),
            reversible_moves: 0,
            en_passant_file: None,
            history: Vec::new(),
            hash: 0,

            added_features: vec![],
            removed_features: vec![],
            should_refresh: true,
        }
    }
}
impl Position {
    /// A position with no pieces.
    pub fn empty() -> Self {
        Self::default()
    }

    /// The initial position of Chess.
    pub fn initial() -> Self {
        Self::from_fen(
            &"rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
                .parse()
                .unwrap(),
        )
    }

    /// Creates a position from a parsed FEN string.
    pub fn from_fen(fen: &Fen) -> Self {
        let mut pieces = [None; 64];
        for sq in Square::squares_iter() {
            pieces[sq as usize] = fen.piece_on(sq).map(|p| p.kind);
        }

        let mut pos = Self {
            pieces,
            bitboards: fen.bitboards,

            side_to_move: fen.side_to_move,
            castling_rights: fen.castling_rights,
            reversible_moves: fen.halfmove_clock as u8,
            en_passant_file: fen.en_passant_file,
            history: Vec::new(),
            hash: 0,

            added_features: vec![],
            removed_features: vec![],
            should_refresh: true,
        };
        pos.rehash();

        pos
    }

    /// Returns a FEN string describing the position.
    pub fn fen(&self) -> Fen {
        Fen {
            bitboards: self.bitboards,
            side_to_move: self.side_to_move,
            castling_rights: self.castling_rights,
            en_passant_file: self.en_passant_file,
            halfmove_clock: self.reversible_moves as u16,
            fullmove_counter: (self.history.len() / 2) as u16,
        }
    }

    /// Adds a piece on the board on the given square.
    ///
    /// # Errors
    /// Returns an error if the square is not empty, or when trying to place a second
    /// king for any side.
    pub fn add_piece(
        &mut self,
        on: Square,
        kind: PieceKind,
        colour: Colour,
    ) -> Result<(), PlaceError> {
        if let Some(p) = self.piece_on(on) {
            return Err(PlaceError::SquareOccupied {
                kind: p.kind,
                colour: p.colour,
            });
        }
        if kind == PieceKind::King {
            return Err(PlaceError::TooManyKings(colour));
        }

        unsafe {
            self.add_piece_unchecked(on, kind, colour);
        }
        Ok(())
    }

    /// Adds a piece on the board on the given square.
    ///
    /// # Safety
    /// Placing a piece on an occupied square will result in undefined behavior.
    pub unsafe fn add_piece_unchecked(&mut self, on: Square, kind: PieceKind, colour: Colour) {
        let bb = on.bitboard();
        *self.piece_bitboard_mut(kind) |= bb;
        *self.color_bitboard_mut(colour) |= bb;
        self.pieces[on as usize] = Some(kind);

        self.hash ^= zobrist::piece_hash(kind, colour, on);
        self.add_piece_feature(kind, on, colour)
    }

    /// Returns the piece kind and color present on a given square if any.
    pub fn piece_on(&self, square: Square) -> Option<Piece> {
        self.pieces[square as usize].map(|kind| {
            let colour = if self.color_bitboard(Colour::Black).is_set(square) {
                Colour::Black
            } else {
                Colour::White
            };
            Piece::new(kind, colour)
        })
    }

    /// Returns the current side to move.
    pub fn side_to_move(&self) -> Colour {
        self.side_to_move
    }

    /// Checks if `action` is legal to play in this position.
    pub fn is_legal(&self, action: Action) -> bool {
        self.actions().contains(&action)
    }

    /// Tries to convert a [`UciMove`] to a usable [`Action`].
    ///
    /// Return `None` if the move was illegal to play in this position.
    pub fn encode_uci(&self, action: UciMove) -> Option<Action> {
        self.actions()
            .iter()
            .find(|a| {
                a.origin() == action.origin
                    && a.target() == action.target
                    && a.promotion_target_type() == action.promoting_to
            })
            .copied()
    }

    /// Tries to convert an [`Action`] to a [`UciMove`].
    ///
    /// Return `None` if the move was illegal to play in this position.
    pub fn decode_uci(&self, action: Action) -> Option<UciMove> {
        if self.is_legal(action) {
            Some(UciMove::from(action))
        } else {
            None
        }
    }

    /// Tries to convert a [`SanMove`] into an [`Action`].
    ///
    /// Returns `None` if the move was illegal in the current position.
    ///
    /// This encoding function is forgiving of missing check/checkmate markers
    /// withing the SAN move notation. It will return the corresponding action
    /// even if there was a checkmate marker and the move is not checkmate, and vice-versa.
    pub fn encode_san(&self, san: SanMove) -> Option<Action> {
        let (origins, target, is_capture, promotion) = match san.move_kind {
            SanMoveKind::PawnPush {
                target,
                promoting_to,
            } => {
                let double_push_rank = if self.side_to_move.is_white() {
                    Rank::Four
                } else {
                    Rank::Five
                };
                let mut origins = vec![if self.side_to_move.is_white() {
                    target + Delta::South
                } else {
                    target + Delta::North
                }];
                if target.rank() == double_push_rank {
                    origins.push(if self.side_to_move.is_white() {
                        target + Delta::South + Delta::South
                    } else {
                        target + Delta::North + Delta::North
                    })
                }
                (origins, target, false, promoting_to)
            }
            SanMoveKind::PawnCapture {
                origin_file,
                target,
                promoting_to,
            } => {
                let origin = if self.side_to_move.is_white() {
                    Square::new(origin_file, target.rank() + Delta::South)
                } else {
                    Square::new(origin_file, target.rank() + Delta::North)
                };
                (vec![origin], target, true, promoting_to)
            }
            SanMoveKind::PieceMove {
                moving_piece,
                origin_file,
                origin_rank,
                is_capture,
                target,
            } => {
                let piece_bb = self.piece_bitboard(moving_piece);
                let colour_bb = self.color_bitboard(self.side_to_move);
                let mut origins_bb = Bitboard::universe();
                if let Some(origin_file) = origin_file {
                    origins_bb &= origin_file.bitboard()
                }
                if let Some(origin_rank) = origin_rank {
                    origins_bb &= origin_rank.bitboard()
                }
                origins_bb &= piece_bb & colour_bb;
                (origins_bb.collect(), target, is_capture, None)
            }
            SanMoveKind::KingSideCastle => {
                if self.side_to_move().is_white() {
                    (vec![Square::E1], Square::G1, false, None)
                } else {
                    (vec![Square::E8], Square::G8, false, None)
                }
            }
            SanMoveKind::QueenSideCastle => {
                if self.side_to_move().is_white() {
                    (vec![Square::E1], Square::C1, false, None)
                } else {
                    (vec![Square::E8], Square::C8, false, None)
                }
            }
        };

        self.actions()
            .iter()
            .find(|a| {
                a.target() == target
                    && a.is_capture() == is_capture
                    && a.promotion_target_type() == promotion
                    && origins.contains(&a.origin())
            })
            .copied()
    }

    /// Tries to convert an [`Action`] into a [`SanMove`].
    ///
    /// Returns `None` if `action` was illegal in the current position.
    ///
    /// This does not encode check/checkmate information into the resulting
    /// [`SanMove`].
    pub fn decode_san(&self, action: Action) -> Option<SanMove> {
        if !self.is_legal(action) {
            return None;
        }

        let moving_piece = self.piece_on(action.origin())?.kind;
        let move_kind = if action.is_kingside_castle() {
            SanMoveKind::KingSideCastle
        } else if action.is_queenside_castle() {
            SanMoveKind::QueenSideCastle
        } else if moving_piece == PieceKind::Pawn {
            if action.is_capture() {
                SanMoveKind::PawnCapture {
                    origin_file: action.origin().file(),
                    target: action.target(),
                    promoting_to: action.promotion_target_type(),
                }
            } else {
                SanMoveKind::PawnPush {
                    target: action.target(),
                    promoting_to: action.promotion_target_type(),
                }
            }
        } else {
            let candidates: Vec<_> = self
                .actions()
                .into_iter()
                .filter_map(|a| {
                    if a.target() == action.target()
                        && self.piece_on(a.origin()).unwrap().kind == moving_piece
                        && a.origin() != action.origin()
                    {
                        Some(a.origin())
                    } else {
                        None
                    }
                })
                .collect();

            let (origin_file, origin_rank) = if candidates.is_empty() {
                // There are no valid candidates for this move
                return None;
            } else if candidates.len() == 1 {
                // No ambiguity
                (None, None)
            } else {
                let file_ambiguity: Vec<_> = candidates
                    .into_iter()
                    .filter(|o| o.file() == action.origin().file())
                    .collect();
                if file_ambiguity.is_empty() {
                    // No file ambiguity
                    (Some(action.origin().file()), None)
                } else {
                    let rank_ambiguity = file_ambiguity
                        .into_iter()
                        .any(|o| o.rank() == action.origin().rank());
                    if !rank_ambiguity {
                        // No rank ambiguity
                        (None, Some(action.origin().rank()))
                    } else {
                        (Some(action.origin().file()), Some(action.origin().rank()))
                    }
                }
            };
            SanMoveKind::PieceMove {
                moving_piece,
                origin_file,
                origin_rank,
                is_capture: action.is_capture(),
                target: action.target(),
            }
        };

        Some(SanMove {
            move_kind,
            check: None,
        })
    }

    /// Makes a move on the board, modifying the position.
    ///
    /// # Errors
    /// This function returns an error if the move is illegal.
    pub fn make<M: ChessMove>(&mut self, action: &M) -> Result<(), IllegalMoveError> {
        if let Some(action) = action.to_action(self) {
            unsafe { self.make_unchecked(action) };
            Ok(())
        } else {
            Err(IllegalMoveError)
        }
    }

    #[inline(always)]
    fn occupied_squares(&self) -> Bitboard {
        self.color_bitboard(Colour::White) | self.color_bitboard(Colour::Black)
    }

    #[inline(always)]
    fn piece_bitboard(&self, kind: PieceKind) -> Bitboard {
        unsafe { *self.bitboards.get_unchecked(kind as usize + 2) }
    }

    #[inline(always)]
    fn piece_bitboard_mut(&mut self, kind: PieceKind) -> &mut Bitboard {
        unsafe { self.bitboards.get_unchecked_mut(kind as usize + 2) }
    }

    #[inline(always)]
    fn color_bitboard(&self, colour: Colour) -> Bitboard {
        unsafe { *self.bitboards.get_unchecked(colour as usize) }
    }

    #[inline(always)]
    fn color_bitboard_mut(&mut self, colour: Colour) -> &mut Bitboard {
        unsafe { self.bitboards.get_unchecked_mut(colour as usize) }
    }

    /// Makes a move on the board, modifying the position.
    ///
    /// # Safety
    /// Passing an illegal move to this function will break the invariants of the
    /// [`Position`] structure, making it unusable.
    #[inline]
    pub unsafe fn make_unchecked(&mut self, mv: Action) {
        let origin = mv.origin();
        let target = mv.target();
        let move_bitboard = origin.bitboard() | target.bitboard();
        let mut moving_kind = unsafe {
            self.pieces
                .get_unchecked(origin as usize)
                .unwrap_unchecked()
        };
        self.should_refresh |= moving_kind == PieceKind::King;

        self.history.push(HistoryEntry {
            played: mv,
            captured: unsafe { *self.pieces.get_unchecked(target as usize) },
            castling_rights: self.castling_rights,
            reversible_moves: self.reversible_moves,
            en_passant_file: self.en_passant_file,
            hash: self.hash,
        });

        // Reset en passant file if any
        if let Some(en_passant_file) = self.en_passant_file.take() {
            self.hash ^= zobrist::en_passant_file_hash(en_passant_file)
        }

        // Modify castling rights if needed
        self.hash ^= self.castling_rights.zobrist_hash();
        for modified in move_bitboard & Bitboard(0x9100000000000091) {
            match modified {
                Square::E1 => self.castling_rights.disallow(Colour::White),
                Square::A1 => self
                    .castling_rights
                    .disallow_queenside_castle(Colour::White),
                Square::H1 => self.castling_rights.disallow_kingside_castle(Colour::White),
                Square::E8 => self.castling_rights.disallow(Colour::Black),
                Square::A8 => self
                    .castling_rights
                    .disallow_queenside_castle(Colour::Black),
                Square::H8 => self.castling_rights.disallow_kingside_castle(Colour::Black),
                _ => unsafe { unreachable_unchecked() },
            }
        }
        self.hash ^= self.castling_rights.zobrist_hash();

        // Take care of move kind specifics
        if let Some(to) = mv.promotion_target() {
            *self.piece_bitboard_mut(PieceKind::Pawn) ^= origin.bitboard();
            *self.piece_bitboard_mut(to) ^= origin.bitboard();
            unsafe {
                *self.pieces.get_unchecked_mut(origin as usize) = Some(to);
            }
            self.hash ^= zobrist::piece_hash(moving_kind, self.side_to_move, origin);
            self.hash ^= zobrist::piece_hash(to, self.side_to_move, origin);
            self.add_piece_feature(to, origin, self.side_to_move);
            self.remove_piece_feature(moving_kind, origin, self.side_to_move);
            moving_kind = to;

            if mv.is_capture() {
                let captured = unsafe {
                    self.pieces
                        .get_unchecked(target as usize)
                        .unwrap_unchecked()
                };
                *self.color_bitboard_mut(self.side_to_move.inverse()) ^= target.bitboard();
                *self.piece_bitboard_mut(captured) ^= target.bitboard();
                self.hash ^= zobrist::piece_hash(captured, self.side_to_move.inverse(), target);
                self.remove_piece_feature(captured, target, self.side_to_move.inverse())
            }
            self.reversible_moves = 0
        } else if mv.is_capture() {
            let target = if mv.special_0_is_set() {
                unsafe {
                    target.translate_unchecked(if self.side_to_move.is_black() {
                        Delta::North
                    } else {
                        Delta::South
                    })
                }
            } else {
                target
            };
            let captured = unsafe {
                self.pieces
                    .get_unchecked(target as usize)
                    .unwrap_unchecked()
            };
            *self.color_bitboard_mut(self.side_to_move.inverse()) ^= target.bitboard();
            *self.piece_bitboard_mut(captured) ^= target.bitboard();
            self.hash ^= zobrist::piece_hash(captured, self.side_to_move.inverse(), target);
            self.remove_piece_feature(captured, target, self.side_to_move.inverse());
            self.reversible_moves = 0
        } else if mv.special_1_is_set() {
            let (rook_origin, rook_target) = if mv.special_0_is_set() {
                if self.side_to_move.is_black() {
                    (Square::A8, Square::D8)
                } else {
                    (Square::A1, Square::D1)
                }
            } else if self.side_to_move.is_black() {
                (Square::H8, Square::F8)
            } else {
                (Square::H1, Square::F1)
            };
            let rook_move = rook_origin.bitboard() | rook_target.bitboard();
            *self.piece_bitboard_mut(PieceKind::Rook) ^= rook_move;
            *self.color_bitboard_mut(self.side_to_move) ^= rook_move;
            unsafe {
                *self.pieces.get_unchecked_mut(rook_target as usize) =
                    self.pieces.get_unchecked_mut(rook_origin as usize).take();
            }
            self.hash ^= zobrist::piece_hash(PieceKind::Rook, self.side_to_move, rook_origin);
            self.hash ^= zobrist::piece_hash(PieceKind::Rook, self.side_to_move, rook_target);
            self.add_piece_feature(PieceKind::Rook, rook_target, self.side_to_move);
            self.remove_piece_feature(PieceKind::Rook, rook_origin, self.side_to_move);
            self.reversible_moves = 0
        } else if mv.special_0_is_set() {
            self.en_passant_file = Some(origin.file());
            self.hash ^= zobrist::en_passant_file_hash(origin.file());
            self.reversible_moves = 0
        } else if moving_kind != PieceKind::Pawn {
            self.reversible_moves += 1
        } else {
            self.reversible_moves = 0
        }

        // Then make the actual move on the board
        *self.color_bitboard_mut(self.side_to_move) ^= move_bitboard;
        *self.piece_bitboard_mut(moving_kind) ^= move_bitboard;
        unsafe {
            *self.pieces.get_unchecked_mut(target as usize) =
                self.pieces.get_unchecked_mut(origin as usize).take();
        }
        self.hash ^= zobrist::piece_hash(moving_kind, self.side_to_move, origin);
        self.hash ^= zobrist::piece_hash(moving_kind, self.side_to_move, target);
        self.add_piece_feature(moving_kind, target, self.side_to_move);
        self.remove_piece_feature(moving_kind, origin, self.side_to_move);

        self.side_to_move.invert();
        self.hash ^= zobrist::side_to_move_hash();
    }

    /// Undoes the last move played, restoring the position as it
    /// was prior to the move.
    ///
    /// If no moves were played prior to calling this function, nothing happens.
    pub fn unmake(&mut self) {
        let Some(HistoryEntry {
            played,
            captured,
            castling_rights,
            reversible_moves,
            en_passant_file,
            hash,
        }) = self.history.pop()
        else {
            return;
        };

        // Restore metadata
        self.castling_rights = castling_rights;
        self.reversible_moves = reversible_moves;
        self.en_passant_file = en_passant_file;
        self.side_to_move.invert();
        self.hash = hash;

        // Unmake the move
        let origin = played.origin();
        let target = played.target();
        let move_bitboard = origin.bitboard() | target.bitboard();
        unsafe {
            *self.pieces.get_unchecked_mut(origin as usize) =
                self.pieces.get_unchecked_mut(target as usize).take()
        };
        let Some(moving_kind) = self.pieces[origin as usize] else {
            unsafe { unreachable_unchecked() }
        };
        *self.color_bitboard_mut(self.side_to_move) ^= move_bitboard;
        *self.piece_bitboard_mut(moving_kind) ^= move_bitboard;
        self.add_piece_feature(moving_kind, origin, self.side_to_move);
        self.remove_piece_feature(moving_kind, target, self.side_to_move);

        // And deal with move kind specifics
        if let Some(to) = played.promotion_target() {
            *self.piece_bitboard_mut(PieceKind::Pawn) ^= origin.bitboard();
            *self.piece_bitboard_mut(to) ^= origin.bitboard();
            unsafe {
                *self.pieces.get_unchecked_mut(origin as usize) = Some(PieceKind::Pawn);
            }
            self.add_piece_feature(PieceKind::Pawn, origin, self.side_to_move);
            self.remove_piece_feature(to, origin, self.side_to_move);

            if played.is_capture() {
                let Some(captured) = captured else {
                    unsafe { unreachable_unchecked() }
                };
                *self.color_bitboard_mut(self.side_to_move.inverse()) ^= target.bitboard();
                *self.piece_bitboard_mut(captured) ^= target.bitboard();
                unsafe {
                    *self.pieces.get_unchecked_mut(target as usize) = Some(captured);
                }
                self.add_piece_feature(captured, target, self.side_to_move.inverse())
            }
        } else if played.is_capture() {
            let target = if played.special_0_is_set() {
                unsafe {
                    target.translate_unchecked(if self.side_to_move.is_black() {
                        Delta::North
                    } else {
                        Delta::South
                    })
                }
            } else {
                target
            };
            let captured = captured.unwrap_or(PieceKind::Pawn);
            *self.color_bitboard_mut(self.side_to_move.inverse()) ^= target.bitboard();
            *self.piece_bitboard_mut(captured) ^= target.bitboard();
            unsafe {
                *self.pieces.get_unchecked_mut(target as usize) = Some(captured);
            }
            self.add_piece_feature(captured, target, self.side_to_move.inverse());
        } else if played.special_1_is_set() {
            let (rook_origin, rook_target) = if played.special_0_is_set() {
                if self.side_to_move.is_black() {
                    (Square::A8, Square::D8)
                } else {
                    (Square::A1, Square::D1)
                }
            } else if self.side_to_move.is_black() {
                (Square::H8, Square::F8)
            } else {
                (Square::H1, Square::F1)
            };
            let rook_move = rook_origin.bitboard() | rook_target.bitboard();
            *self.piece_bitboard_mut(PieceKind::Rook) ^= rook_move;
            *self.color_bitboard_mut(self.side_to_move) ^= rook_move;
            unsafe {
                *self.pieces.get_unchecked_mut(rook_origin as usize) =
                    self.pieces.get_unchecked_mut(rook_target as usize).take()
            };
            self.add_piece_feature(PieceKind::Rook, rook_origin, self.side_to_move);
            self.remove_piece_feature(PieceKind::Rook, rook_target, self.side_to_move);
        }
    }

    /// Returns attack information for the side to move.
    #[inline]
    pub fn attack_information(&self) -> AttackInformation {
        let us = self.color_bitboard(self.side_to_move);
        let them = self.color_bitboard(self.side_to_move.inverse());
        let occupied = us | them;
        let king_square = self.king_square(self.side_to_move);
        let king = king_square.bitboard();

        let (pawn_east_attack, pawn_west_attack) = Self::pawn_attacks(self.side_to_move);

        let mut attacked = Bitboard::empty();
        let mut checkers = Bitboard::empty();
        let mut check_rays = Bitboard::empty();
        let mut pinned = Bitboard::empty();
        let mut movable_pins = heapless::Vec::new();

        // First, fill the `attacked` board with info from direct contact pieces.
        // Those pieces do not generate rays and thus cannot be blocked or create pins.
        let ennemy_pawns = self.piece_bitboard(PieceKind::Pawn) & them;
        attacked |= ((ennemy_pawns & !File::H.bitboard()) - pawn_west_attack)
            | ((ennemy_pawns & !File::A.bitboard()) - pawn_east_attack);

        let ennemy_knights = self.piece_bitboard(PieceKind::Knight) & them;
        for origin in ennemy_knights {
            attacked |= knight_moves(origin)
        }

        // If any of those attacked squares intersects with our king, we find the checkers
        // and add them to the `capturable` set.
        if attacked.intersects(king) {
            checkers |= knight_moves(king_square) & ennemy_knights;
            checkers |= (((king & !File::H.bitboard()) + pawn_east_attack)
                | ((king & !File::A.bitboard()) + pawn_west_attack))
                & ennemy_pawns;
        }

        // The enemy king cannot check us legally,
        // but we still need to compute the squares it attacks.
        attacked |= king_moves(self.king_square(self.side_to_move.inverse()));

        // We then deal with ray attacks. These can produce pins and are blockable.
        // For each sliding piece, we generate its moves and then check for two scenarios:
        // - either the piece directly attacks our king, we're in check and add the slider to the `capturable` set.
        // - or the piece can attack our king when xraying our pieces. In this case, the slider might create a pin.

        // We need to xray our king to account for slide-aways attacked squares.
        let non_king = occupied ^ king;

        // Diagonal attackers
        let ennemy_bishops = self.piece_bitboard(PieceKind::Bishop) & them;
        let ennemy_rooks = self.piece_bitboard(PieceKind::Rook) & them;
        let ennemy_queens = self.piece_bitboard(PieceKind::Queen) & them;

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
                checkers |= origin.bitboard();
                check_rays |= diagonal_moves(origin, occupied) & king_diagonal_rays;
            }
            // This piece is accessible by our king when ignoring our own pieces, so it
            // might create a pin. This is checked by counting the number of our own pieces
            // intersected by the ray.
            else if king_diagonal_rays.is_set(origin) {
                let ray = diagonal_moves(origin, king) & king_diagonal_rays;
                let pin = ray & us;

                // If the ray is blocked by more than one friendly piece, they
                // are not pinned and we don't add the pinned piece.
                if pin.is_single_populated() {
                    pinned |= pin;

                    // If the piece can move along the ray and we're not already in check,
                    // add it to the movable pins
                    if checkers.is_empty() {
                        // SAFETY: we already checked that there is a set square.
                        let pinned_square = unsafe { pin.lowest_set_square_unchecked() };

                        let Some(kind) = self.pieces[pinned_square as usize] else {
                            panic!(
                                "Detected pin on {pinned_square} with ray\n{ray:?}\nbut there is no piece here\n{self}"
                            );
                        };
                        if kind.is_diagonal_slider() || kind == PieceKind::Pawn {
                            let movable_ray = (ray ^ pin) | origin.bitboard();
                            unsafe {
                                movable_pins.push_unchecked((pinned_square, movable_ray));
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
                checkers |= origin.bitboard();
                check_rays |= king_orthogonal_rays & orthogonal_moves(origin, occupied);
            }
            // This piece is accessible by our king when ignoring our own pieces, so it
            // might create a pin. This is checked by counting the number of our own pieces
            // intersected by the ray.
            else if king_orthogonal_rays.is_set(origin) {
                let ray = orthogonal_moves(origin, king) & king_orthogonal_rays;
                let pin = ray & us;
                if pin.is_single_populated() {
                    pinned |= pin;

                    // If the piece can move along the ray and we're not already in check,
                    // add it to the movable pins
                    if checkers.is_empty() {
                        // SAFETY: we already checked that there is a set square.
                        let pinned_square = unsafe { pin.lowest_set_square_unchecked() };

                        let Some(kind) = self.pieces[pinned_square as usize] else {
                            panic!(
                                "Detected pin on {pinned_square} with ray\n{ray:?}\nbut there is no piece here\n{self}"
                            );
                        };
                        if kind.is_orthogonal_slider() || kind == PieceKind::Pawn {
                            let movable_ray = (ray ^ pin) | origin.bitboard();
                            unsafe {
                                movable_pins.push_unchecked((pinned_square, movable_ray));
                            }
                        }
                    }
                }
            }
        }

        AttackInformation {
            checkers,
            check_rays,
            attacked,
            pinned,
            movable_pins,
        }
    }

    /// Returns the result of the game in the current position, or `None` if the
    /// game is not finished.
    ///
    /// The only two kind of draws that are not checked by this method are:
    /// - draws agreed to by both players
    /// - timeout draws
    pub fn game_result(&self) -> Option<GameResult> {
        if self.fifty_move_draw() {
            return Some(GameResult::Draw(DrawKind::FiftyMoveRule));
        }
        if self.threefold_repetition() {
            return Some(GameResult::Draw(DrawKind::Repetition));
        }
        if self.insufficient_material() {
            return Some(GameResult::Draw(DrawKind::InsufficientMaterial));
        }
        if self.actions().is_empty() {
            if self.attack_information().in_check() {
                Some(GameResult::Checkmate(self.side_to_move))
            } else {
                Some(GameResult::Draw(DrawKind::Stalemate))
            }
        } else {
            None
        }
    }

    /// Returns the pawn push delta for the given colour.
    #[inline(always)]
    const fn pawn_push(colour: Colour) -> Delta {
        if colour.is_black() {
            Delta::South
        } else {
            Delta::North
        }
    }

    /// Pawn attacks deltas for the given colour.
    #[inline(always)]
    const fn pawn_attacks(colour: Colour) -> (Delta, Delta) {
        if colour.is_black() {
            (Delta::SouthEast, Delta::SouthWest)
        } else {
            (Delta::NorthEast, Delta::NorthWest)
        }
    }

    /// Returns the pawns double push rank for the given colour.
    #[inline(always)]
    const fn pawn_double_push_rank(colour: Colour) -> Rank {
        if colour.is_black() {
            Rank::Six
        } else {
            Rank::Three
        }
    }

    /// Returns the pawns promotion rank for the given colour.
    #[inline(always)]
    const fn pawn_promotion_rank(colour: Colour) -> Rank {
        if colour.is_black() {
            Rank::Two
        } else {
            Rank::Seven
        }
    }

    /// Generates a list of legal moves in the current position.
    ///
    /// If this function returns an empty list, the side to move is in stalemate or checkmate.
    /// This can be checked using [`Position::attack_information`].
    pub fn actions(&self) -> ActionList {
        let mut moves = ActionList::new();

        // Initialize some generally useful constants.
        let mut us = self.color_bitboard(self.side_to_move);
        let them = self.color_bitboard(self.side_to_move.inverse());
        let occupied = us | them;
        let free = !occupied;

        let king_square = self.king_square(self.side_to_move);

        let attacks = self.attack_information();

        // Remove pinned pieces from normal move generation
        us ^= attacks.pinned;

        // Decide what to do based on the number of checkers.
        // If more than one checker, no moves other than the king's are legal.
        // Otherwise, we generate moves as we generally do.
        let mut capturable = them;
        let mut movable = free;
        if attacks.in_check() {
            capturable = attacks.checkers;
            movable = attacks.check_rays;
        } else {
            // If no checker we can generate castling moves and pinned pieces moves
            if self.queenside_castle_allowed(self.side_to_move, attacks.attacked) {
                unsafe { moves.push_unchecked(Action::new_queenside_castle(self.side_to_move)) }
            }
            if self.kingside_castle_allowed(self.side_to_move, attacks.attacked) {
                unsafe { moves.push_unchecked(Action::new_kingside_castle(self.side_to_move)) }
            }

            for (sq, ray) in &attacks.movable_pins {
                let movable = ray & free;
                let capturable = ray & them;
                let origin = sq.bitboard();
                match self.pieces[*sq as usize] {
                    Some(PieceKind::Pawn) => {
                        self.generate_pawn_moves(&mut moves, origin, movable, capturable);
                        if let Some(file) = self.en_passant_file {
                            self.generate_en_passant_captures(
                                &mut moves, origin, file, movable, capturable,
                            )
                        }
                    }
                    Some(PieceKind::Bishop) => {
                        self.generate_diagonal_moves(&mut moves, origin, movable, capturable)
                    }
                    Some(PieceKind::Rook) => {
                        self.generate_orthogonal_moves(&mut moves, origin, movable, capturable)
                    }
                    Some(PieceKind::Queen) => {
                        self.generate_diagonal_moves(&mut moves, origin, movable, capturable);
                        self.generate_orthogonal_moves(&mut moves, origin, movable, capturable);
                    }
                    _ => unreachable!(),
                }
            }
        }

        // We generate moves for all pieces only if we're not in double check
        if !attacks.in_double_check() {
            let pawns = self.piece_bitboard(PieceKind::Pawn) & us;
            self.generate_pawn_moves(&mut moves, pawns, movable, capturable);
            if let Some(file) = self.en_passant_file {
                self.generate_en_passant_captures(&mut moves, pawns, file, movable, capturable)
            }

            let knights = self.piece_bitboard(PieceKind::Knight) & us;
            self.generate_knight_moves(&mut moves, knights, movable, capturable);

            let queens = self.piece_bitboard(PieceKind::Queen) & us;
            let orthogonal_sliders = queens | (self.piece_bitboard(PieceKind::Rook) & us);
            self.generate_orthogonal_moves(&mut moves, orthogonal_sliders, movable, capturable);

            let diagonal_sliders = queens | (self.piece_bitboard(PieceKind::Bishop) & us);
            self.generate_diagonal_moves(&mut moves, diagonal_sliders, movable, capturable);
        }

        // We always generate king moves.
        let king_moves = king_moves(king_square) & !attacks.attacked;
        Self::serialize_piece_moves(&mut moves, king_square, king_moves, free, them);

        moves
    }

    #[inline(always)]
    fn serialize_piece_moves(
        moves: &mut ActionList,
        origin: Square,
        targets: Bitboard,
        movable: Bitboard,
        capturable: Bitboard,
    ) {
        let quiets = (targets & movable).map(|t| Action::new_quiet(origin, t));
        moves.extend(quiets);
        let captures = (targets & capturable).map(|t| Action::new_capture(origin, t));
        moves.extend(captures);
    }

    #[inline(always)]
    fn generate_diagonal_moves(
        &self,
        moves: &mut ActionList,
        diagonal_sliders: Bitboard,
        movable: Bitboard,
        capturable: Bitboard,
    ) {
        for origin in diagonal_sliders {
            let diagonal_moves = diagonal_moves(origin, self.occupied_squares());
            Self::serialize_piece_moves(moves, origin, diagonal_moves, movable, capturable);
        }
    }

    #[inline(always)]
    fn generate_orthogonal_moves(
        &self,
        moves: &mut ActionList,
        orthogonal_sliders: Bitboard,
        movable: Bitboard,
        capturable: Bitboard,
    ) {
        for origin in orthogonal_sliders {
            let orthogonal_moves = orthogonal_moves(origin, self.occupied_squares());
            Self::serialize_piece_moves(moves, origin, orthogonal_moves, movable, capturable);
        }
    }

    #[inline(always)]
    fn generate_knight_moves(
        &self,
        moves: &mut ActionList,
        knights: Bitboard,
        movable: Bitboard,
        capturable: Bitboard,
    ) {
        for origin in knights {
            let knight_moves = knight_moves(origin);
            Self::serialize_piece_moves(moves, origin, knight_moves, movable, capturable);
        }
    }

    /// Generates pawn moves.
    #[inline(always)]
    fn generate_pawn_moves(
        &self,
        moves: &mut ActionList,
        pawns: Bitboard,
        movable: Bitboard,
        capturable: Bitboard,
    ) {
        // GENERAL SAFETY: calls to `push_unchecked` are ok, we can't generate too many moves.

        let promoting = pawns & Self::pawn_promotion_rank(self.side_to_move).bitboard();
        let double_push_rank = Self::pawn_double_push_rank(self.side_to_move).bitboard();
        let push = Self::pawn_push(self.side_to_move);
        let (east_attack, west_attack) = Self::pawn_attacks(self.side_to_move);

        // Remove promoting pawns from the pawn list to deal with them separately.
        let pawns = pawns ^ promoting;

        let single_push_targets = (pawns + push) & !self.occupied_squares();
        let single_push_origins = (single_push_targets & movable) - push;
        for (o, t) in single_push_origins.zip(single_push_targets & movable) {
            unsafe { moves.push_unchecked(Action::new_quiet(o, t)) }
        }
        let double_push_targets = ((single_push_targets & double_push_rank) + push) & movable;
        let double_push_origins = double_push_targets - push - push;
        for (o, t) in double_push_origins.zip(double_push_targets) {
            unsafe { moves.push_unchecked(Action::new_double_push(o, t)) }
        }

        let east_captures_targets = ((pawns & !File::H.bitboard()) + east_attack) & capturable;
        let east_captures_origins = east_captures_targets - east_attack;

        for (o, t) in east_captures_origins.zip(east_captures_targets) {
            unsafe { moves.push_unchecked(Action::new_capture(o, t)) }
        }
        let west_captures_targets = ((pawns & !File::A.bitboard()) + west_attack) & capturable;
        let west_captures_origins = west_captures_targets - west_attack;
        for (o, t) in west_captures_origins.zip(west_captures_targets) {
            unsafe { moves.push_unchecked(Action::new_capture(o, t)) }
        }

        // Same for promoting pawns
        let promoting_push_targets = (promoting + push) & movable;
        let promoting_push_origins = promoting_push_targets - push;
        for (origin, target) in promoting_push_origins.zip(promoting_push_targets) {
            for m in Action::new_promotions(origin, target) {
                unsafe { moves.push_unchecked(m) }
            }
        }
        let promoting_east_captures_targets =
            ((promoting & !File::H.bitboard()) + east_attack) & capturable;
        let promoting_east_captures_origins = promoting_east_captures_targets - east_attack;
        for (origin, target) in promoting_east_captures_origins.zip(promoting_east_captures_targets)
        {
            for m in Action::new_promotion_captures(origin, target) {
                unsafe { moves.push_unchecked(m) }
            }
        }
        let promoting_west_captures_targets =
            ((promoting & !File::A.bitboard()) + west_attack) & capturable;
        let promoting_west_captures_origins = promoting_west_captures_targets - west_attack;
        for (origin, target) in promoting_west_captures_origins.zip(promoting_west_captures_targets)
        {
            for m in Action::new_promotion_captures(origin, target) {
                unsafe { moves.push_unchecked(m) }
            }
        }
    }

    #[inline(always)]
    fn generate_en_passant_captures(
        &self,
        moves: &mut ActionList,
        pawns: Bitboard,
        file: File,
        movable: Bitboard,
        capturable: Bitboard,
    ) {
        // En passant is a bit tricky as it can leave the king in check.
        // Those moves are rare enough that we can check carefully for illegal
        // en passant capture without caring too much about the cost.
        let (target_rank, capture_rank) = if self.side_to_move.is_black() {
            (Rank::Three.bitboard(), Rank::Four.bitboard())
        } else {
            (Rank::Six.bitboard(), Rank::Five.bitboard())
        };
        let captured = file.bitboard() & capture_rank;
        // SAFETY: we know that there is at least one set square.
        let target = unsafe { (file.bitboard() & target_rank).lowest_set_square_unchecked() };

        if captured.intersects(capturable) || movable.is_set(target) {
            let ennemy_orthogonals = (self.piece_bitboard(PieceKind::Queen)
                | self.piece_bitboard(PieceKind::Rook))
                & self.color_bitboard(self.side_to_move.inverse());
            let east_attacker = ((captured & !File::H.bitboard()) + Delta::East) & pawns;
            let west_attacker = ((captured & !File::A.bitboard()) + Delta::West) & pawns;

            if !capture_rank.is_set(self.king_square(self.side_to_move)) {
                if let Some(origin) = east_attacker.lowest_set_square() {
                    unsafe { moves.push_unchecked(Action::new_en_passant(origin, target)) }
                }

                if let Some(origin) = west_attacker.lowest_set_square() {
                    unsafe { moves.push_unchecked(Action::new_en_passant(origin, target)) }
                }
            } else {
                // Check if the king could be attacked if the attacked and attacker
                // left the board
                if !(orthogonal_moves(
                    self.king_square(self.side_to_move),
                    self.occupied_squares() & !(captured | east_attacker),
                ) & capture_rank)
                    .intersects(ennemy_orthogonals)
                {
                    if let Some(origin) = east_attacker.lowest_set_square() {
                        unsafe { moves.push_unchecked(Action::new_en_passant(origin, target)) }
                    }
                }
                // Same for west attacks
                if !(orthogonal_moves(
                    self.king_square(self.side_to_move),
                    self.occupied_squares() & !(captured | west_attacker),
                ) & capture_rank)
                    .intersects(ennemy_orthogonals)
                {
                    if let Some(origin) = west_attacker.lowest_set_square() {
                        unsafe { moves.push_unchecked(Action::new_en_passant(origin, target)) }
                    }
                }
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

    /// Checks if the position is a "dead position" aka no side can force checkmate
    /// due to insufficient material.
    ///
    /// It checks for the following scenarios:
    /// - King vs King
    /// - King + Minor piece vs King
    /// - King + Bishop vs King + Bishop (bishops of the same color)
    ///
    /// Note that this function is purely material based and follows Article 5.2.2 of
    /// the FIDE rules. It does not account for likely draws.
    pub fn insufficient_material(&self) -> bool {
        // Bare king on both sides
        if self.color_bitboard(Colour::White).cardinality() == 1
            && self.color_bitboard(Colour::Black).cardinality() == 1
        {
            return true;
        }

        let knights = self.piece_bitboard(PieceKind::Knight);
        let bishops = self.piece_bitboard(PieceKind::Bishop);
        let others = [PieceKind::Pawn, PieceKind::Rook, PieceKind::Queen]
            .into_iter()
            .fold(Bitboard::empty(), |acc, kind| {
                acc | self.piece_bitboard(kind)
            });
        let white_pieces = self.color_bitboard(Colour::White);
        let black_pieces = self.color_bitboard(Colour::Black);

        let white_others_count = (others & white_pieces).cardinality();
        let black_others_count = (others & black_pieces).cardinality();

        if white_others_count != 0 && black_others_count != 0 {
            let white_knights_count = (knights & white_pieces).cardinality();
            let black_knights_count = (knights & black_pieces).cardinality();
            let white_bishops_count = (bishops & white_pieces).cardinality();
            let black_bishops_count = (bishops & black_pieces).cardinality();
            let white_minor_pieces = white_bishops_count + white_knights_count;
            let black_minor_pieces = black_bishops_count + black_knights_count;
            return match (white_minor_pieces, black_minor_pieces) {
                (0, 1) | (1, 0) => true,
                (1, 1) => {
                    let bishops_on_dark_squares =
                        self.piece_bitboard(PieceKind::Bishop) & Square::DARK_SQUARES;
                    white_bishops_count == 1
                        && black_bishops_count == 1
                        && bishops_on_dark_squares.cardinality() != 1
                }
                _ => false,
            };
        }

        false
    }

    /// Returns `true` if the NNUE accumulator should be refreshed.
    #[allow(dead_code)]
    pub(crate) fn should_refresh_features(&self) -> bool {
        self.should_refresh
    }

    /// Clears accumulated NNUE features and refresh flag.
    #[allow(dead_code)]
    pub(crate) fn clear_features(&mut self) {
        self.should_refresh = false;
        self.added_features.clear();
        self.removed_features.clear();
    }

    /// Returns a vector of active NNUE feature indices for this position.
    #[allow(dead_code)]
    pub(crate) fn active_features(&self, perspective: Colour) -> Vec<u16> {
        let mut features = vec![];
        let king_square = self.king_square(perspective);

        for colour in [Colour::Black, Colour::White] {
            let colour_bb = self.color_bitboard(colour);
            for piece_kind in [
                PieceKind::Pawn,
                PieceKind::Knight,
                PieceKind::Bishop,
                PieceKind::Rook,
                PieceKind::Queen,
            ] {
                for piece_square in self.piece_bitboard(piece_kind) & colour_bb {
                    features.push(feature_index(king_square, piece_square, piece_kind, colour))
                }
            }
        }
        features
    }

    /// Returns accumulated added NNUE features.
    #[allow(dead_code)]
    pub(crate) fn added_features(&self) -> &[u16] {
        &self.added_features
    }

    /// Returns accumulated removed NNUE features.
    #[allow(dead_code)]
    pub(crate) fn removed_features(&self) -> &[u16] {
        &self.removed_features
    }

    #[inline(always)]
    fn add_piece_feature(&mut self, kind: PieceKind, square: Square, colour: Colour) {
        if self.should_refresh {
            return;
        }

        self.added_features
            .push(piece_feature_index(square, kind, colour));
    }

    #[inline(always)]
    fn remove_piece_feature(&mut self, kind: PieceKind, square: Square, colour: Colour) {
        if self.should_refresh {
            return;
        }

        self.removed_features
            .push(piece_feature_index(square, kind, colour))
    }

    /// Returns the position of the king of the given colour.
    #[inline]
    pub fn king_square(&self, perspective: Colour) -> Square {
        let king = self.piece_bitboard(PieceKind::King) & self.color_bitboard(perspective);
        unsafe { king.lowest_set_square_unchecked() }
    }

    /// Checks if the side can castle queenside.
    #[inline]
    pub fn queenside_castle_allowed(&self, side: Colour, attacked: Bitboard) -> bool {
        if side.is_black() {
            self.castling_rights.queenside_castle_allowed(Colour::Black)
                && !self
                    .occupied_squares()
                    .intersects(Bitboard(0xe00000000000000))
                && !attacked.intersects(Bitboard(0xc00000000000000))
        } else {
            self.castling_rights.queenside_castle_allowed(Colour::White)
                && !self.occupied_squares().intersects(Bitboard(0xe))
                && !attacked.intersects(Bitboard(0xc))
        }
    }
    /// Checks if the side can castle kingside.
    #[inline]
    pub fn kingside_castle_allowed(&self, side: Colour, attacked: Bitboard) -> bool {
        if side.is_black() {
            self.castling_rights.kingside_castle_allowed(Colour::Black)
                && !self
                    .occupied_squares()
                    .intersects(Bitboard(0x6000000000000000))
                && !attacked.intersects(Bitboard(0x6000000000000000))
        } else {
            self.castling_rights.kingside_castle_allowed(Colour::White)
                && !self.occupied_squares().intersects(Bitboard(0x60))
                && !attacked.intersects(Bitboard(0x60))
        }
    }

    /// Returns the Zobrist hash of the position.
    #[inline(always)]
    pub fn zobrist_hash(&self) -> u64 {
        self.hash
    }

    /// Hashes the position from 0.
    #[inline]
    fn rehash(&mut self) {
        self.hash = 0;
        for sq in Square::squares_iter() {
            if let Some(p) = self.piece_on(sq) {
                self.hash ^= zobrist::piece_hash(p.kind, p.colour, sq)
            }
        }

        self.hash ^= self.castling_rights.zobrist_hash();
        if self.side_to_move.is_black() {
            self.hash ^= zobrist::side_to_move_hash();
        }

        if let Some(ep) = self.en_passant_file {
            self.hash ^= zobrist::en_passant_file_hash(ep)
        }
    }
}
impl std::hash::Hash for Position {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.hash.hash(state)
    }
}
impl From<Fen> for Position {
    fn from(value: Fen) -> Self {
        Self::from_fen(&value)
    }
}
impl From<&Fen> for Position {
    fn from(value: &Fen) -> Self {
        Self::from_fen(value)
    }
}
impl std::fmt::Debug for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (r, rank) in Rank::iter().rev().enumerate() {
            for sq in Square::rank_squares_iter(rank) {
                write!(f, "{} ", match self.piece_on(sq) {
                    None => ".".to_string(),
                    Some(p) => p.to_string(),
                })?
            }
            match r {
                3 => writeln!(
                    f,
                    "side to move: {}",
                    if self.side_to_move.is_black() {
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
        writeln!(f, "\nfen: {}", self.fen())
    }
}
impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[cfg(test)]
mod test {
    use crate::chess::{action::Action, square::Square};

    use super::Position;

    #[test]
    fn hash_test() {
        let mut pos = Position::initial();
        let og_hash = pos.zobrist_hash();
        pos.make(&Action::new_double_push(Square::E2, Square::E4))
            .unwrap();
        pos.unmake();
        assert_eq!(og_hash, pos.zobrist_hash())
    }
}
