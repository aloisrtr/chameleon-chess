//! Main API to represent and interact with a chess position.
//!
//! This includes making, unmaking and generating moves, defining positions from
//! FEN strings, etc.
use crate::brain::feature::{feature_index, piece_feature_index};
use std::hint::unreachable_unchecked;

use super::{
    action::Action,
    bitboard::Bitboard,
    castling_rights::CastlingRights,
    colour::Colour,
    fen::{Fen, FenError},
    history::HistoryEntry,
    magic_tables::*,
    piece::PieceKind,
    square::{Delta, File, Rank, Square},
    zobrist,
};

pub type ActionList = heapless::Vec<Action, 256>;

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
// TODO: More precise errors
pub struct IllegalMoveError;

pub enum PlaceError {
    SquareOccupied { kind: PieceKind, colour: Colour },
    TooManyKings(Colour),
}

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

    /// Returns `true` if there is at least one checker.
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
            piece_bitboards: [Bitboard::empty(); 6],
            color_bitboards: [Bitboard::empty(); 2],
            occupancy_bitboard: Bitboard::empty(),

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

    /// The initial position of chess.
    pub fn initial() -> Self {
        Self::from_fen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1").unwrap()
    }

    /// Creates a position from a FEN string.
    /// # Errors
    /// This function returns an error if the FEN string passed is invalid or badly
    /// formatted.
    pub fn from_fen(fen: &str) -> Result<Self, FenError> {
        let fen: Fen = fen.parse()?;

        let mut color_bitboards = [Bitboard::empty(); 2];
        color_bitboards.copy_from_slice(&fen.bitboards[0..2]);
        let mut piece_bitboards = [Bitboard::empty(); 6];
        piece_bitboards.copy_from_slice(&fen.bitboards[2..]);
        let mut pieces = [None; 64];
        for sq in Square::squares_fen_iter() {
            pieces[sq as usize] = fen.piece_on(sq).map(|(k, _)| k);
        }

        let mut pos = Self {
            pieces,
            color_bitboards,
            piece_bitboards,
            occupancy_bitboard: color_bitboards[0] | color_bitboards[1],

            side_to_move: fen.side_to_move,
            castling_rights: fen.castling_rights,
            reversible_moves: fen.halfmove_clock as u8,
            en_passant_file: fen.en_passant.map(|ep| ep.file()),
            history: Vec::new(),
            hash: 0,

            added_features: vec![],
            removed_features: vec![],
            should_refresh: true,
        };
        pos.rehash();

        Ok(pos)
    }

    /// Returns a FEN string describing the position.
    pub fn fen(&self) -> String {
        let mut bitboards = [Bitboard::empty(); 8];
        bitboards.copy_from_slice(self.color_bitboards.as_slice());
        bitboards[2..].copy_from_slice(self.piece_bitboards.as_slice());
        Fen {
            bitboards,
            side_to_move: self.side_to_move,
            castling_rights: self.castling_rights,
            en_passant: self.en_passant_file.map(|file| {
                Square::new(
                    file,
                    if self.side_to_move.is_white() {
                        Rank::Six
                    } else {
                        Rank::Three
                    },
                )
            }),
            halfmove_clock: self.reversible_moves as u16,
            fullmove_counter: (self.history.len() / 2) as u16,
        }
        .to_string()
    }

    /// Adds a piece on the board on the given square.
    /// # Errors
    /// Returns an error if the square is not empty, or when trying to place a second
    /// king for any side.
    pub fn add_piece(
        &mut self,
        on: Square,
        kind: PieceKind,
        colour: Colour,
    ) -> Result<(), PlaceError> {
        todo!()
    }

    /// Adds a piece on the board on the given square.
    /// # Safety
    /// Placing a piece on an occupied square will result in undefined behavior.
    pub unsafe fn add_piece_unchecked(&mut self, on: Square, kind: PieceKind, colour: Colour) {
        let bb = on.bitboard();
        self.piece_bitboards[kind as usize] |= bb;
        self.color_bitboards[colour as usize] |= bb;
        self.occupancy_bitboard |= bb;
        self.pieces[on as usize] = Some(kind);

        self.hash ^= if colour.is_black() {
            zobrist::piece_hash::<true>(kind, on)
        } else {
            zobrist::piece_hash::<false>(kind, on)
        };

        self.add_piece_feature(kind, on, colour)
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

    /// Returns the current side to move.
    pub fn side_to_move(&self) -> Colour {
        self.side_to_move
    }

    /// Makes a move on the board, modifying the position.
    /// # Errors
    /// This function returns an error if the move is illegal.
    pub fn make(&mut self, action: Action) -> Result<(), IllegalMoveError> {
        if let Some(&mv) = self.actions().iter().find(|mv| {
            mv.origin() == action.origin()
                && mv.target() == action.target()
                && mv.promotion_target() == action.promotion_target()
        }) {
            unsafe {
                self.make_unchecked(mv);
            }
            Ok(())
        } else {
            Err(IllegalMoveError)
        }
    }

    /// Makes a move on the board, modifying the position.
    /// # Safety
    /// Passing an illegal move to this function will break the invariants of the
    /// [`Position`] structure, making it unusable.
    #[inline]
    pub unsafe fn make_unchecked(&mut self, mv: Action) {
        #[inline(always)]
        unsafe fn make_unchecked_generic<const BLACK_TO_MOVE: bool>(
            position: &mut Position,
            mv: Action,
        ) {
            let origin = mv.origin();
            let target = mv.target();
            let move_bitboard = origin.bitboard() | target.bitboard();
            let Some(mut moving_kind) = position.pieces.get_unchecked(origin as usize) else {
                unreachable_unchecked()
            };
            position.should_refresh |= moving_kind == PieceKind::King;

            let us_index = BLACK_TO_MOVE as usize;
            let them_index = !BLACK_TO_MOVE as usize;
            let perspective = if BLACK_TO_MOVE {
                Colour::Black
            } else {
                Colour::White
            };

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
            if let Some(to) = mv.promotion_target() {
                *position
                    .piece_bitboards
                    .get_unchecked_mut(PieceKind::Pawn as usize) ^= origin.bitboard();
                *position.piece_bitboards.get_unchecked_mut(to as usize) ^= origin.bitboard();
                *position.pieces.get_unchecked_mut(origin as usize) = Some(to);
                position.hash ^= zobrist::piece_hash::<BLACK_TO_MOVE>(moving_kind, origin);
                position.hash ^= zobrist::piece_hash::<BLACK_TO_MOVE>(to, origin);
                position.add_piece_feature(to, origin, perspective);
                position.remove_piece_feature(moving_kind, origin, perspective);
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
                    position.remove_piece_feature(captured, target, perspective.inverse())
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
                position.remove_piece_feature(captured, target, perspective.inverse());
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
                position.add_piece_feature(PieceKind::Rook, rook_target, perspective);
                position.remove_piece_feature(PieceKind::Rook, rook_origin, perspective);
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
            position.add_piece_feature(moving_kind, target, perspective);
            position.remove_piece_feature(moving_kind, origin, perspective);

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
            position.add_piece_feature(moving_kind, origin, position.side_to_move);
            position.remove_piece_feature(moving_kind, target, position.side_to_move);

            // And deal with move kind specifics
            if let Some(to) = played.promotion_target() {
                *position
                    .piece_bitboards
                    .get_unchecked_mut(PieceKind::Pawn as usize) ^= origin.bitboard();
                *position.piece_bitboards.get_unchecked_mut(to as usize) ^= origin.bitboard();
                *position.pieces.get_unchecked_mut(origin as usize) = Some(PieceKind::Pawn);
                position.add_piece_feature(PieceKind::Pawn, origin, position.side_to_move);
                position.remove_piece_feature(to, origin, position.side_to_move);

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
                    position.add_piece_feature(captured, target, position.side_to_move.inverse())
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
                position.add_piece_feature(captured, target, position.side_to_move.inverse());
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
                position.add_piece_feature(PieceKind::Rook, rook_origin, position.side_to_move);
                position.remove_piece_feature(PieceKind::Rook, rook_target, position.side_to_move);
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

    /// Returns check information for the side to move.
    pub fn attack_information(&self) -> AttackInformation {
        let us = self.color_bitboards[self.side_to_move as usize];
        let them = self.color_bitboards[self.side_to_move.inverse() as usize];
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
        let ennemy_pawns = self.piece_bitboards[PieceKind::Pawn as usize] & them;
        attacked |= ((ennemy_pawns & !File::H.bitboard()) - pawn_west_attack)
            | ((ennemy_pawns & !File::A.bitboard()) - pawn_east_attack);

        let ennemy_knights = self.piece_bitboards[PieceKind::Knight as usize] & them;
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
        let non_king = self.occupancy_bitboard ^ king;

        // Diagonal attacks
        let ennemy_bishops = self.piece_bitboards[PieceKind::Bishop as usize] & them;
        let ennemy_rooks = self.piece_bitboards[PieceKind::Rook as usize] & them;
        let ennemy_queens = self.piece_bitboards[PieceKind::Queen as usize] & them;

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
                check_rays |= diagonal_moves(origin, self.occupancy_bitboard) & king_diagonal_rays;
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

                        let kind = self.pieces[pinned_square as usize].unwrap();
                        if kind.is_diagonal_slider() || kind == PieceKind::Pawn {
                            let movable_ray = ray ^ pin | origin.bitboard();
                            movable_pins.push((pinned_square, movable_ray));
                        }
                    }
                }

                // Then generate its moves (if any) if we're not already in check.
                // if checkers.is_empty() {
                //     let movable_ray = ray ^ pinned;
                //     let pinned_square = pinned.lowest_set_square_unchecked();

                //     // If the pinned piece is a corresponding slider, move it along the
                //     // ray and generate a capture
                //     if self.pieces[pinned_square as usize]
                //         .unwrap()
                //         .is_diagonal_slider()
                //     {
                //         for m in movable_ray.map(|t| LegalAction::new_quiet(pinned_square, t)) {
                //             moves.push_unchecked(m)
                //         }
                //         moves.push_unchecked(LegalAction::new_capture(pinned_square, origin))
                //     }
                //     // If the pinned piece is a pawn, it can only capture the piece directly
                //     // or capture en passant. Note that captures can be promotions.
                //     else if position.pieces[pinned_square as usize] == Some(PieceKind::Pawn) {
                //         if ((pinned & !File::H.bitboard()) + pawn_east_attack).is_set(origin)
                //             || ((pinned & !File::A.bitboard()) + pawn_west_attack).is_set(origin)
                //         {
                //             // Promotion capture
                //             if pinned.intersects(promotion_rank) {
                //                 for m in LegalAction::new_promotion_capture(pinned_square, origin) {
                //                     moves.push_unchecked(m)
                //                 }
                //             } else {
                //                 moves
                //                     .push_unchecked(LegalAction::new_capture(pinned_square, origin))
                //             }
                //         }

                //         // En passant captures.
                //         // We first check if the target is on the pin ray.
                //         // If it is, we then check if the pawn to be captured
                //         // doesn't discover a check
                //         if let Some(file) = position.en_passant_file {
                //             let (target_rank, capture_rank) = if BLACK_TO_MOVE {
                //                 (Rank::Three.bitboard(), Rank::Four.bitboard())
                //             } else {
                //                 (Rank::Six.bitboard(), Rank::Five.bitboard())
                //             };
                //             let captured = file.bitboard() & capture_rank;
                //             let target =
                //                 (file.bitboard() & target_rank).lowest_set_square_unchecked();
                //             let capturers = ((captured & !File::H.bitboard()) + Delta::East)
                //                 | ((captured & !File::A.bitboard()) + Delta::West);

                //             if movable_ray.is_set(target) && capturers.is_set(pinned_square) {
                //                 moves.push_unchecked(LegalAction::new_en_passant(origin, target))
                //             }
                //         }
                //     }
                // }
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
                check_rays |=
                    king_orthogonal_rays & orthogonal_moves(origin, self.occupancy_bitboard);
            }
            // This piece is accessible by our king when ignoring our own pieces, so it
            // might create a pin. This is checked by counting the number of our own pieces
            // intersected by the ray.
            else if king_orthogonal_rays.is_set(origin) {
                let ray = orthogonal_moves(origin, king) & king_orthogonal_rays;
                let pin = ray & us;
                if pin.is_single_populated() {
                    pinned |= pin;
                }

                // If the piece can move along the ray and we're not already in check,
                // add it to the movable pins
                if checkers.is_empty() {
                    // SAFETY: we already checked that there is a set square.
                    let pinned_square = unsafe { pin.lowest_set_square_unchecked() };

                    let kind = self.pieces[pinned_square as usize].unwrap();
                    if kind.is_diagonal_slider() || kind == PieceKind::Pawn {
                        let movable_ray = ray ^ pin | origin.bitboard();
                        movable_pins.push((pinned_square, movable_ray));
                    }
                }

                // Then generate its moves (if any) if we're not already in check.
                // if checkers.is_empty() {
                //     let movable_ray = ray ^ pinned;
                //     let pinned_square = pinned.lowest_set_square_unchecked();
                //     // If the pinned piece is a corresponding slider, move it along the
                //     // ray and generate a capture
                //     if position.pieces[pinned_square as usize]
                //         .unwrap_unchecked()
                //         .is_orthogonal_slider()
                //     {
                //         for m in movable_ray.map(|t| LegalAction::new_quiet(pinned_square, t)) {
                //             moves.push_unchecked(m)
                //         }
                //         moves.push_unchecked(LegalAction::new_capture(pinned_square, origin))
                //     }
                //     // If the pinned piece is a pawn, it can only push or double push
                //     // if its on its original square.
                //     else if position.pieces[pinned_square as usize] == Some(PieceKind::Pawn) {
                //         let single_push = pinned + pawn_push;
                //         if let Some(target) = (single_push & movable_ray).next() {
                //             moves.push_unchecked(LegalAction::new_quiet(pinned_square, target));
                //             if let Some(target) = (((single_push & double_push_rank) + pawn_push)
                //                 & movable_ray)
                //                 .lowest_set_square()
                //             {
                //                 moves.push_unchecked(LegalAction::new_double_push(
                //                     pinned_square,
                //                     target,
                //                 ))
                //             }
                //         }
                //     }
                // }
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

    /// Returns the pawn push delta for the given colour.
    #[inline(always)]
    pub const fn pawn_push(colour: Colour) -> Delta {
        if colour.is_black() {
            Delta::South
        } else {
            Delta::North
        }
    }

    /// Pawn attacks deltas for the given colour.
    #[inline(always)]
    pub const fn pawn_attacks(colour: Colour) -> (Delta, Delta) {
        if colour.is_black() {
            (Delta::SouthEast, Delta::SouthWest)
        } else {
            (Delta::NorthEast, Delta::NorthWest)
        }
    }

    /// Returns the pawns double push rank for the given colour.
    #[inline(always)]
    pub const fn pawn_double_push_rank(colour: Colour) -> Rank {
        if colour.is_black() {
            Rank::Six
        } else {
            Rank::Three
        }
    }

    /// Returns the pawns promotion rank for the given colour.
    #[inline(always)]
    pub const fn pawn_promotion_rank(colour: Colour) -> Rank {
        if colour.is_black() {
            Rank::Two
        } else {
            Rank::Seven
        }
    }

    /// Generates a list of legal moves in the current position.
    ///
    /// If this function returns an empty list, the side to move is in stalemate or checkmate.
    /// An additional flag is returned for this situation: if `true`, the side to move
    /// is in check.
    pub fn actions(&self) -> ActionList {
        let mut moves = ActionList::new();

        // Initialize some generally useful constants.
        let mut us = self.color_bitboards[self.side_to_move as usize];
        let them = self.color_bitboards[self.side_to_move.inverse() as usize];

        let king_square = self.king_square(self.side_to_move);
        let king = king_square.bitboard();

        let attacks = self.attack_information();

        // Remove pinned pieces from normal move generation
        us ^= attacks.pinned;

        // Decide what to do based on the number of checkers.
        // If more than one checker, no moves other than the king's are legal.
        // Otherwise, we generate moves as we generally do.
        let mut capturable = them;
        let mut movable = !self.occupancy_bitboard;
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
                let movable = ray & !self.occupancy_bitboard;
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
                        self.generate_diagonal_moves(&mut moves, origin, movable, capturable)
                    }
                    _ => unreachable!(),
                }
            }
        }

        // We generate moves for all pieces only if we're not in double check
        if !attacks.in_double_check() {
            let pawns = self.piece_bitboards[PieceKind::Pawn as usize] & us;
            self.generate_pawn_moves(&mut moves, pawns, movable, capturable);
            if let Some(file) = self.en_passant_file {
                self.generate_en_passant_captures(&mut moves, pawns, file, movable, capturable)
            }

            let knights = self.piece_bitboards[PieceKind::Knight as usize] & us;
            self.generate_knight_moves(&mut moves, knights, movable, capturable);

            let queens = self.piece_bitboards[PieceKind::Queen as usize] & us;
            let orthogonal_sliders = queens | (self.piece_bitboards[PieceKind::Rook as usize] & us);
            self.generate_orthogonal_moves(&mut moves, orthogonal_sliders, movable, capturable);

            let diagonal_sliders = queens | (self.piece_bitboards[PieceKind::Bishop as usize] & us);
            self.generate_diagonal_moves(&mut moves, diagonal_sliders, movable, capturable);
        }

        // We always generate king moves.
        let king_moves = king_moves(king_square) & !attacks.attacked;
        for m in (king_moves & !self.occupancy_bitboard).map(|t| Action::new_quiet(king_square, t))
        {
            unsafe { moves.push_unchecked(m) }
        }
        for m in (king_moves & them).map(|t| Action::new_capture(king_square, t)) {
            unsafe { moves.push_unchecked(m) }
        }

        moves
    }

    fn generate_diagonal_moves(
        &self,
        moves: &mut ActionList,
        diagonal_sliders: Bitboard,
        movable: Bitboard,
        capturable: Bitboard,
    ) {
        // GENERAL SAFETY: calls to `push_unchecked` are ok, we can't generate too many moves.
        for origin in diagonal_sliders {
            let diagonal_moves = diagonal_moves(origin, self.occupancy_bitboard);
            for m in (diagonal_moves & movable).map(|t| Action::new_quiet(origin, t)) {
                unsafe { moves.push_unchecked(m) }
            }
            for m in (diagonal_moves & capturable).map(|t| Action::new_capture(origin, t)) {
                unsafe { moves.push_unchecked(m) }
            }
        }
    }

    fn generate_orthogonal_moves(
        &self,
        moves: &mut ActionList,
        orthogonal_sliders: Bitboard,
        movable: Bitboard,
        capturable: Bitboard,
    ) {
        // GENERAL SAFETY: calls to `push_unchecked` are ok, we can't generate too many moves.
        for origin in orthogonal_sliders {
            let orthogonal_moves = orthogonal_moves(origin, self.occupancy_bitboard);
            for m in (orthogonal_moves & movable).map(|t| Action::new_quiet(origin, t)) {
                unsafe { moves.push_unchecked(m) }
            }
            for m in (orthogonal_moves & capturable).map(|t| Action::new_capture(origin, t)) {
                unsafe { moves.push_unchecked(m) }
            }
        }
    }

    fn generate_knight_moves(
        &self,
        moves: &mut ActionList,
        knights: Bitboard,
        movable: Bitboard,
        capturable: Bitboard,
    ) {
        // GENERAL SAFETY: calls to `push_unchecked` are ok, we can't generate too many moves.
        for origin in knights {
            let knight_moves = knight_moves(origin);
            for m in (knight_moves & movable).map(|t| Action::new_quiet(origin, t)) {
                unsafe { moves.push_unchecked(m) }
            }
            for m in (knight_moves & capturable).map(|t| Action::new_capture(origin, t)) {
                unsafe { moves.push_unchecked(m) }
            }
        }
    }

    /// Generates pawn moves.
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

        let single_push_targets = (pawns + push) & !self.occupancy_bitboard;
        let single_push_origins = (single_push_targets & movable) - push;
        for m in single_push_origins
            .zip(single_push_targets & movable)
            .map(|(o, t)| Action::new_quiet(o, t))
        {
            unsafe { moves.push_unchecked(m) }
        }
        let double_push_targets = ((single_push_targets & double_push_rank) + push) & movable;
        let double_push_origins = double_push_targets - push - push;
        for m in double_push_origins
            .zip(double_push_targets)
            .map(|(o, t)| Action::new_double_push(o, t))
        {
            unsafe { moves.push_unchecked(m) }
        }

        let east_captures_targets = ((pawns & !File::H.bitboard()) + east_attack) & capturable;
        let east_captures_origins = east_captures_targets - east_attack;

        for m in east_captures_origins
            .zip(east_captures_targets)
            .map(|(o, t)| Action::new_capture(o, t))
        {
            unsafe { moves.push_unchecked(m) }
        }
        let west_captures_targets = ((pawns & !File::A.bitboard()) + west_attack) & capturable;
        let west_captures_origins = west_captures_targets - west_attack;
        for m in west_captures_origins
            .zip(west_captures_targets)
            .map(|(o, t)| Action::new_capture(o, t))
        {
            unsafe { moves.push_unchecked(m) }
        }

        // Same for promoting pawns
        let promoting_push_targets = (promoting + push) & movable;
        let promoting_push_origins = promoting_push_targets - push;
        for (origin, target) in promoting_push_origins.zip(promoting_push_targets) {
            for m in Action::new_promotion(origin, target) {
                unsafe { moves.push_unchecked(m) }
            }
        }
        let promoting_east_captures_targets =
            ((promoting & !File::H.bitboard()) + east_attack) & capturable;
        let promoting_east_captures_origins = promoting_east_captures_targets - east_attack;
        for (origin, target) in promoting_east_captures_origins.zip(promoting_east_captures_targets)
        {
            for m in Action::new_promotion_capture(origin, target) {
                unsafe { moves.push_unchecked(m) }
            }
        }
        let promoting_west_captures_targets =
            ((promoting & !File::A.bitboard()) + west_attack) & capturable;
        let promoting_west_captures_origins = promoting_west_captures_targets - west_attack;
        for (origin, target) in promoting_west_captures_origins.zip(promoting_west_captures_targets)
        {
            for m in Action::new_promotion_capture(origin, target) {
                unsafe { moves.push_unchecked(m) }
            }
        }
    }

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
            let ennemy_orthogonals = (self.piece_bitboards[PieceKind::Queen as usize]
                | self.piece_bitboards[PieceKind::Rook as usize])
                & self.color_bitboards[self.side_to_move.inverse() as usize];
            let east_attacker = ((captured & !File::H.bitboard()) + Delta::East) & pawns;
            let west_attacker = ((captured & !File::A.bitboard()) + Delta::West) & pawns;

            // Check if the king could be attacked if the attacked and attacker
            // left the board
            if !(orthogonal_moves(
                self.king_square(self.side_to_move),
                self.occupancy_bitboard & !captured & !east_attacker,
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
                self.occupancy_bitboard & !captured & !west_attacker,
            ) & capture_rank)
                .intersects(ennemy_orthogonals)
            {
                if let Some(origin) = west_attacker.lowest_set_square() {
                    unsafe { moves.push_unchecked(Action::new_en_passant(origin, target)) }
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

    /// Returns `true` if the accumulator should be refreshed.
    pub fn should_refresh_features(&self) -> bool {
        self.should_refresh
    }

    /// Clears accumulated features and refresh flag.
    pub fn clear_features(&mut self) {
        self.should_refresh = false;
        self.added_features.clear();
        self.removed_features.clear();
    }

    /// Returns a vector of active feature indices for this position.
    pub fn active_features(&self, perspective: Colour) -> Vec<u16> {
        let mut features = vec![];
        let king_square = self.king_square(perspective);

        for colour in [Colour::Black, Colour::White] {
            let colour_bb = self.color_bitboards[colour as usize];
            for piece_kind in [
                PieceKind::Pawn,
                PieceKind::Knight,
                PieceKind::Bishop,
                PieceKind::Rook,
                PieceKind::Queen,
            ] {
                for piece_square in self.piece_bitboards[piece_kind as usize] & colour_bb {
                    features.push(feature_index(king_square, piece_square, piece_kind, colour))
                }
            }
        }
        features
    }

    /// Returns accumulated added features.
    pub fn added_features(&self) -> &[u16] {
        &self.added_features
    }

    /// Returns accumulated removed features.
    pub fn removed_features(&self) -> &[u16] {
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
        let king = self.piece_bitboards[PieceKind::King as usize]
            & self.color_bitboards[perspective as usize];
        unsafe { king.lowest_set_square_unchecked() }
    }

    /// Checks if the side can castle queenside.
    #[inline]
    pub fn queenside_castle_allowed(&self, side: Colour, attacked: Bitboard) -> bool {
        if side.is_black() {
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
    #[inline]
    pub fn kingside_castle_allowed(&self, side: Colour, attacked: Bitboard) -> bool {
        if side.is_black() {
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

    /// Hashes the position from 0.
    #[inline]
    fn rehash(&mut self) {
        self.hash = 0;
        for sq in Square::squares_iter() {
            if let Some((kind, colour)) = self.piece_on(sq) {
                self.hash ^= if colour.is_black() {
                    zobrist::piece_hash::<true>(kind, sq)
                } else {
                    zobrist::piece_hash::<false>(kind, sq)
                };
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
impl std::fmt::Debug for Position {
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
                        if color.is_black() {
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
impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[cfg(test)]
mod test {
    use crate::game::{action::Action, square::Square};

    use super::Position;

    #[test]
    fn hash_test() {
        let mut pos = Position::initial();
        let og_hash = pos.zobrist_hash();
        pos.make(Action::new_double_push(Square::E2, Square::E4))
            .unwrap();
        pos.unmake();
        assert_eq!(og_hash, pos.zobrist_hash())
    }
}
