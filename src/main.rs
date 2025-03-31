// src/main.rs
use serde::{Deserialize, Serialize};
use std::collections::HashMap; // Keep for move history repetition check for draw claim
use std::error::Error;
use std::fmt;
use std::fs;
use std::hash::Hash; // Required for HashMap key, even if we use Zobrist for game state repetition
use std::io::{self, Write};
use std::time::{Duration, Instant};
use std::boxed::Box;
use rand::{SeedableRng, RngCore}; // Added RngCore for random()
use rand::rngs::StdRng;
use lazy_static::lazy_static; // For global precomputed tables and Zobrist table

// --- Constants ---
const INITIAL_TIME_SECONDS: u64 = 15 * 60; // 15 minutes
const DEFAULT_STATS_FILENAME: &str = "chess_stats.json";

// --- Bitboard Constants ---
const FILE_A: u64 = 0x0101010101010101;
const FILE_B: u64 = FILE_A << 1;
const FILE_G: u64 = FILE_A << 6;
const FILE_H: u64 = FILE_A << 7;

const RANK_1: u64 = 0x00000000000000FF;
const RANK_2: u64 = RANK_1 << 8;
const RANK_3: u64 = RANK_1 << 16; // Needed for EP Zobrist and maybe logic
const RANK_4: u64 = RANK_1 << 24; // Needed for EP logic
const RANK_5: u64 = RANK_1 << 32; // Needed for EP logic
const RANK_6: u64 = RANK_1 << 40; // Needed for EP Zobrist and maybe logic
const RANK_7: u64 = RANK_1 << 48;
const RANK_8: u64 = RANK_1 << 56;

const NOT_FILE_A: u64 = !FILE_A;
const NOT_FILE_B: u64 = !FILE_B;
const NOT_FILE_G: u64 = !FILE_G;
const NOT_FILE_H: u64 = !FILE_H;

// Added missing NOT_RANK constants
const NOT_RANK_1: u64 = !RANK_1;
const NOT_RANK_2: u64 = !RANK_2;
const NOT_RANK_7: u64 = !RANK_7;
const NOT_RANK_8: u64 = !RANK_8;

// Square indices for castling
const WHITE_KING_START: u8 = 4; // e1
const WHITE_KS_ROOK_START: u8 = 7; // h1
const WHITE_QS_ROOK_START: u8 = 0; // a1
const WHITE_KING_KS_CASTLE_DEST: u8 = 6; // g1
const WHITE_KING_QS_CASTLE_DEST: u8 = 2; // c1

const BLACK_KING_START: u8 = 60; // e8
const BLACK_KS_ROOK_START: u8 = 63; // h8
const BLACK_QS_ROOK_START: u8 = 56; // a8
const BLACK_KING_KS_CASTLE_DEST: u8 = 62; // g8
const BLACK_KING_QS_CASTLE_DEST: u8 = 58; // c8


// Directions for sliding piece attacks/pins
const DIRECTIONS: &[(i8, i8, bool)] = &[ // (dr, df, is_diagonal)
    ( 1,  0, false), ( -1,  0, false), ( 0,  1, false), ( 0, -1, false), // Orthogonal
    ( 1,  1, true),  ( 1, -1, true),  (-1,  1, true),  (-1, -1, true),  // Diagonal
];


// --- Enums and Basic Structs ---
#[derive(Debug, Serialize, Deserialize, Copy, Clone, PartialEq, Eq, Hash)]
enum Color { White, Black }

impl Color {
    fn opponent(&self) -> Color {
        match self { Color::White => Color::Black, Color::Black => Color::White }
    }
    fn index(&self) -> usize { // Helper for Zobrist indexing
        match self { Color::White => 0, Color::Black => 1 }
    }
}

#[derive(Debug, Serialize, Deserialize, Copy, Clone, PartialEq, Eq, Hash)]
enum PieceType { Pawn, Knight, Bishop, Rook, Queen, King }

impl PieceType {
     fn index(&self) -> usize { // Helper for Zobrist indexing
        match self {
            PieceType::Pawn => 0, PieceType::Knight => 1, PieceType::Bishop => 2,
            PieceType::Rook => 3, PieceType::Queen => 4, PieceType::King => 5,
        }
    }
}

#[derive(Debug, Serialize, Deserialize, Copy, Clone, PartialEq, Eq, Hash)]
struct Piece {
    kind: PieceType,
    color: Color,
}

impl Piece {
    fn new(kind: PieceType, color: Color) -> Self { Piece { kind, color } }
    fn value(&self) -> u32 {
        match self.kind {
            PieceType::Pawn => 1, PieceType::Knight => 3, PieceType::Bishop => 3,
            PieceType::Rook => 5, PieceType::Queen => 9, PieceType::King => 0, // King value irrelevant for material count usually
        }
    }
    #[allow(dead_code)] // Potentially useful later (e.g., FEN)
    fn from_char(c: char) -> Option<Self> {
        let color = if c.is_uppercase() { Color::White } else { Color::Black };
        let kind = match c.to_ascii_lowercase() {
            'p' => PieceType::Pawn, 'n' => PieceType::Knight, 'b' => PieceType::Bishop,
            'r' => PieceType::Rook, 'q' => PieceType::Queen, 'k' => PieceType::King,
            _ => return None,
        };
        Some(Piece::new(kind, color))
    }
}

impl fmt::Display for Piece {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let symbol = match self.kind {
            PieceType::Pawn => 'p', PieceType::Knight => 'n', PieceType::Bishop => 'b',
            PieceType::Rook => 'r', PieceType::Queen => 'q', PieceType::King => 'k',
        };
        let symbol = match self.color {
            Color::White => symbol.to_ascii_uppercase(),
            Color::Black => symbol,
        };
        write!(f, "{}", symbol)
    }
}

// Helper to convert square index (0-63) to algebraic notation (e.g., "e4")
fn index_to_algebraic(index: u8) -> String {
    if index >= 64 { return "??".to_string(); }
    let rank = index / 8;
    let file = index % 8;
    let file_char = (b'a' + file) as char;
    let rank_char = (b'1' + rank) as char;
    format!("{}{}", file_char, rank_char)
}

// Helper to convert algebraic notation to square index (0-63)
fn algebraic_to_index(s: &str) -> Option<u8> {
    if s.len() != 2 { return None; }
    let mut chars = s.chars();
    let file_char = chars.next()?;
    let rank_char = chars.next()?;
    let file = match file_char { 'a'..='h' => Some(file_char as u8 - b'a'), _ => None }?;
    let rank = match rank_char { '1'..='8' => Some(rank_char as u8 - b'1'), _ => None }?;
    Some(rank * 8 + file)
}

// --- Move Representation ---
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
struct Move {
    from_sq: u8, // Square index 0-63
    to_sq: u8,   // Square index 0-63
    promotion: Option<PieceType>,
    // Flag for simple move ordering (determined during pseudo-legal generation)
    #[serde(skip)] // Don't serialize this helper field
    is_capture: bool,
    // Flag to indicate if this move represents castling (determined during generation)
    #[serde(skip)]
    is_castle: bool,
}

impl Move {
    /// Creates a standard move. `is_capture` should reflect if the `to_sq` is occupied by an opponent.
    fn new(from_sq: u8, to_sq: u8, promotion: Option<PieceType>, is_capture: bool) -> Self {
        // Determine if it's a *potential* castling move based on king movement pattern
        // This is a basic check; legality is confirmed elsewhere.
        let is_castle = (from_sq == WHITE_KING_START && (to_sq == WHITE_KING_KS_CASTLE_DEST || to_sq == WHITE_KING_QS_CASTLE_DEST)) ||
                        (from_sq == BLACK_KING_START && (to_sq == BLACK_KING_KS_CASTLE_DEST || to_sq == BLACK_KING_QS_CASTLE_DEST));
        Move { from_sq, to_sq, promotion, is_capture, is_castle }
    }

    /// Special constructor for moves *known* to be castling (generated during king move generation).
    fn new_castle(from_sq: u8, to_sq: u8) -> Self {
        Move { from_sq, to_sq, promotion: None, is_capture: false, is_castle: true }
    }

    /// Returns the standard algebraic notation for the move.
    fn to_algebraic_string(&self) -> String {
        if self.is_castle {
            if self.to_sq == WHITE_KING_KS_CASTLE_DEST || self.to_sq == BLACK_KING_KS_CASTLE_DEST {
                "O-O".to_string() // Kingside castle
            } else {
                "O-O-O".to_string() // Queenside castle
            }
        } else {
            format!("{}{}{}",
                index_to_algebraic(self.from_sq),
                index_to_algebraic(self.to_sq),
                self.promotion.map_or(String::new(), |p| match p {
                    PieceType::Queen => "q", PieceType::Rook => "r",
                    PieceType::Bishop => "b", PieceType::Knight => "n",
                    _ => "", // King/Pawn promotion invalid, should be caught earlier
                }.to_string())
            )
        }
    }
}


// --- Precomputed Move Tables ---

lazy_static! {
    static ref KNIGHT_ATTACKS: [u64; 64] = compute_knight_attacks();
    static ref KING_ATTACKS: [u64; 64] = compute_king_attacks();
    // static ref PAWN_ATTACKS: [[u64; 64]; 2] = compute_pawn_attacks(); // Could add if needed
    static ref ZOBRIST: ZobristTable = ZobristTable::new();
}

fn compute_knight_attacks() -> [u64; 64] {
    let mut attacks = [0u64; 64];
    for sq in 0..64 {
        let from_bb = 1u64 << sq;
        let mut moves: u64 = 0;
        // Offsets: 17, 15, 10, 6, -17, -15, -10, -6
        // Apply masks to prevent wrapping around the board edges incorrectly
        moves |= (from_bb & NOT_FILE_H & NOT_RANK_7 & NOT_RANK_8).wrapping_shl(17); // Up 2 Right 1
        moves |= (from_bb & NOT_FILE_A & NOT_RANK_7 & NOT_RANK_8).wrapping_shl(15); // Up 2 Left 1
        moves |= (from_bb & NOT_FILE_G & NOT_FILE_H & NOT_RANK_8).wrapping_shl(10); // Up 1 Right 2
        moves |= (from_bb & NOT_FILE_A & NOT_FILE_B & NOT_RANK_8).wrapping_shl(6);  // Up 1 Left 2
        moves |= (from_bb & NOT_FILE_A & NOT_RANK_1 & NOT_RANK_2).wrapping_shr(17); // Down 2 Left 1
        moves |= (from_bb & NOT_FILE_H & NOT_RANK_1 & NOT_RANK_2).wrapping_shr(15); // Down 2 Right 1
        moves |= (from_bb & NOT_FILE_A & NOT_FILE_B & NOT_RANK_1).wrapping_shr(10); // Down 1 Left 2
        moves |= (from_bb & NOT_FILE_G & NOT_FILE_H & NOT_RANK_1).wrapping_shr(6);  // Down 1 Right 2

        attacks[sq as usize] = moves;
    }
    attacks
}


fn compute_king_attacks() -> [u64; 64] {
    let mut attacks = [0u64; 64];
    for sq in 0..64 {
        let from_bb = 1u64 << sq;
        let mut moves: u64 = 0;
        // Apply masks to prevent wrapping
        moves |= (from_bb & NOT_FILE_A & NOT_RANK_8).wrapping_shl(7); // Up-Left
        moves |= (from_bb             & NOT_RANK_8).wrapping_shl(8); // Up
        moves |= (from_bb & NOT_FILE_H & NOT_RANK_8).wrapping_shl(9); // Up-Right
        moves |= (from_bb & NOT_FILE_A            ).wrapping_shr(1); // Left
        moves |= (from_bb & NOT_FILE_H            ).wrapping_shl(1); // Right
        moves |= (from_bb & NOT_FILE_A & NOT_RANK_1).wrapping_shr(9); // Down-Left
        moves |= (from_bb             & NOT_RANK_1).wrapping_shr(8); // Down
        moves |= (from_bb & NOT_FILE_H & NOT_RANK_1).wrapping_shr(7); // Down-Right
        attacks[sq as usize] = moves;
    }
    attacks
}

// --- Zobrist Hashing ---
#[derive(Debug, Clone)]
struct ZobristTable {
    // piece[color][piece_type][square]
    piece_keys: [[[u64; 64]; 6]; 2],
    // castling_keys[white_kingside][white_queenside][black_kingside][black_queenside]
    // Using indices 0/1 for false/true
    castling_keys: [[[[u64; 2]; 2]; 2]; 2],
    // en_passant_keys[square] - XOR with 0 if no en passant target square
    // Keys only generated for valid target squares (rank 3 and 6), others are 0.
    en_passant_keys: [u64; 64],
    black_to_move_key: u64,
}

impl ZobristTable {
    fn new() -> Self {
        // Use a fixed seed for reproducibility during development/testing
        let mut rng = StdRng::seed_from_u64(0xDEADBEEFCAFEBABE); // Fixed seed
        let mut table = ZobristTable {
            piece_keys: [[([0; 64]); 6]; 2],
            castling_keys: [[[[0; 2]; 2]; 2]; 2],
            en_passant_keys: [0; 64], // Index 0..63 correspond to target EP squares a3..h3 / a6..h6
            black_to_move_key: rng.next_u64(),
        };

        for color in 0..2 {
            for piece_type in 0..6 {
                for square in 0..64 {
                    table.piece_keys[color][piece_type][square] = rng.next_u64();
                }
            }
        }

        for wk in 0..2 {
            for wq in 0..2 {
                for bk in 0..2 {
                    for bq in 0..2 {
                        table.castling_keys[wk][wq][bk][bq] = rng.next_u64();
                    }
                }
            }
        }

        // Only generate keys for valid EP target squares (ranks 3 and 6)
        for file in 0..8 {
             // Calculate square index based on rank constant and file offset
             let sq_rank3 = (RANK_3.trailing_zeros() + file) as usize;
             if sq_rank3 < 64 { table.en_passant_keys[sq_rank3] = rng.next_u64(); }
             let sq_rank6 = (RANK_6.trailing_zeros() + file) as usize;
             if sq_rank6 < 64 { table.en_passant_keys[sq_rank6] = rng.next_u64(); }
        }

        table
    }

    #[inline(always)]
    fn piece(&self, piece: Piece, sq: u8) -> u64 {
        // Bounds check only needed if sq could be invalid; assuming 0-63 here.
        self.piece_keys[piece.color.index()][piece.kind.index()][sq as usize]
    }

    #[inline(always)]
    fn castling(&self, rights: CastlingRights) -> u64 {
        self.castling_keys[rights.white_kingside as usize][rights.white_queenside as usize]
                          [rights.black_kingside as usize][rights.black_queenside as usize]
    }

    /// Get Zobrist key for en passant target square. Returns 0 if no EP target or target is invalid.
    #[inline(always)]
    fn en_passant(&self, ep_square: Option<u8>) -> u64 {
        match ep_square {
            Some(sq) if sq < 64 => self.en_passant_keys[sq as usize], // Access valid index
            _ => 0, // No target or invalid square index
        }
    }

    /// Get Zobrist key component for side to move. Returns 0 for White.
    #[inline(always)]
    fn side_to_move(&self, color: Color) -> u64 {
        if color == Color::Black { self.black_to_move_key } else { 0 }
    }
}

// --- Bitboard State ---

#[derive(Debug, Serialize, Deserialize, Copy, Clone, PartialEq, Eq, Hash)]
struct CastlingRights {
    white_kingside: bool, white_queenside: bool,
    black_kingside: bool, black_queenside: bool,
}

impl CastlingRights {
    fn initial() -> Self { Self { white_kingside: true, white_queenside: true, black_kingside: true, black_queenside: true } }

    // Update rights based on king move
    fn king_moved(&mut self, color: Color) {
        if color == Color::White {
            self.white_kingside = false;
            self.white_queenside = false;
        } else {
            self.black_kingside = false;
            self.black_queenside = false;
        }
    }

    // Removed unused `rook_moved_or_captured` method. The logic is handled
    // directly within apply_legal_move and apply_move_immutable_no_zobrist.
    // fn rook_moved_or_captured(&mut self, square_index: u8) { ... }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct BitboardState {
    wp: u64, wn: u64, wb: u64, wr: u64, wq: u64, wk: u64, // White pieces
    bp: u64, bn: u64, bb: u64, br: u64, bq: u64, bk: u64, // Black pieces
    white_occupied: u64,
    black_occupied: u64,
    occupied: u64,
    turn: Color,
    castling_rights: CastlingRights,
    en_passant_square: Option<u8>, // Target square index (if any)
    halfmove_clock: u32,
    fullmove_number: u32,
}

impl BitboardState {
    /// Creates the initial board state.
    fn initial() -> Self {
        let wp = RANK_2;
        let wn = (1 << 1) | (1 << 6);
        let wb = (1 << 2) | (1 << 5);
        let wr = (1 << WHITE_QS_ROOK_START) | (1 << WHITE_KS_ROOK_START);
        let wq = 1 << 3;
        let wk = 1 << WHITE_KING_START;

        let bp = RANK_7;
        let bn = ((1 << 1) | (1 << 6)) << 56;
        let bb = ((1 << 2) | (1 << 5)) << 56;
        let br = (1 << BLACK_QS_ROOK_START) | (1 << BLACK_KS_ROOK_START);
        let bq = (1 << 3) << 56;
        let bk = 1 << BLACK_KING_START;

        let white_occupied = wp | wn | wb | wr | wq | wk;
        let black_occupied = bp | bn | bb | br | bq | bk;
        let occupied = white_occupied | black_occupied;

        BitboardState {
            wp, wn, wb, wr, wq, wk,
            bp, bn, bb, br, bq, bk,
            white_occupied, black_occupied, occupied,
            turn: Color::White,
            castling_rights: CastlingRights::initial(),
            en_passant_square: None,
            halfmove_clock: 0,
            fullmove_number: 1,
        }
    }

    /// Recalculates occupancy bitboards from piece bitboards.
    /// Call this after modifying piece bitboards directly.
    #[inline(always)]
    fn update_occupancy(&mut self) {
        self.white_occupied = self.wp | self.wn | self.wb | self.wr | self.wq | self.wk;
        self.black_occupied = self.bp | self.bn | self.bb | self.br | self.bq | self.bk;
        self.occupied = self.white_occupied | self.black_occupied;
    }

     /// Returns the bitboard for a specific piece type and color.
    #[inline(always)]
    fn get_piece_board(&self, piece_type: PieceType, color: Color) -> u64 {
        match (color, piece_type) {
            (Color::White, PieceType::Pawn) => self.wp,
            (Color::White, PieceType::Knight) => self.wn,
            (Color::White, PieceType::Bishop) => self.wb,
            (Color::White, PieceType::Rook) => self.wr,
            (Color::White, PieceType::Queen) => self.wq,
            (Color::White, PieceType::King) => self.wk,
            (Color::Black, PieceType::Pawn) => self.bp,
            (Color::Black, PieceType::Knight) => self.bn,
            (Color::Black, PieceType::Bishop) => self.bb,
            (Color::Black, PieceType::Rook) => self.br,
            (Color::Black, PieceType::Queen) => self.bq,
            (Color::Black, PieceType::King) => self.bk,
        }
    }

    /// Returns a mutable reference to the bitboard for a specific piece type and color.
    #[inline(always)]
    fn get_piece_board_mut(&mut self, piece_type: PieceType, color: Color) -> &mut u64 {
        match (color, piece_type) {
            (Color::White, PieceType::Pawn) => &mut self.wp,
            (Color::White, PieceType::Knight) => &mut self.wn,
            (Color::White, PieceType::Bishop) => &mut self.wb,
            (Color::White, PieceType::Rook) => &mut self.wr,
            (Color::White, PieceType::Queen) => &mut self.wq,
            (Color::White, PieceType::King) => &mut self.wk,
            (Color::Black, PieceType::Pawn) => &mut self.bp,
            (Color::Black, PieceType::Knight) => &mut self.bn,
            (Color::Black, PieceType::Bishop) => &mut self.bb,
            (Color::Black, PieceType::Rook) => &mut self.br,
            (Color::Black, PieceType::Queen) => &mut self.bq,
            (Color::Black, PieceType::King) => &mut self.bk,
        }
    }

    /// Sets a bit on the specified piece bitboard. XORs Zobrist key.
    /// Assumes the square was previously empty of this piece.
    fn set_piece_at(&mut self, sq: u8, piece_type: PieceType, color: Color, zobrist_key: &mut u64) {
        let bb = self.get_piece_board_mut(piece_type, color);
        let mask = 1u64 << sq;
        if *bb & mask == 0 { // Avoid double XOR if setting where piece already exists (shouldn't happen in normal flow)
            *bb |= mask;
            *zobrist_key ^= ZOBRIST.piece(Piece::new(piece_type, color), sq);
        }
    }

    /// Clears a bit from ALL bitboards (used when capturing or moving).
    /// Returns the Piece that was at that square, if any. XORs Zobrist key if piece found.
    fn clear_square(&mut self, sq: u8, zobrist_key: &mut u64) -> Option<Piece> {
        let mask = 1u64 << sq;
        let inv_mask = !mask;
        let mut captured = None;

        // Check and clear piece bitboards, storing the piece if found
        if self.wp & mask != 0 { self.wp &= inv_mask; captured = Some(Piece::new(PieceType::Pawn, Color::White)); }
        else if self.wn & mask != 0 { self.wn &= inv_mask; captured = Some(Piece::new(PieceType::Knight, Color::White)); }
        else if self.wb & mask != 0 { self.wb &= inv_mask; captured = Some(Piece::new(PieceType::Bishop, Color::White)); }
        else if self.wr & mask != 0 { self.wr &= inv_mask; captured = Some(Piece::new(PieceType::Rook, Color::White)); }
        else if self.wq & mask != 0 { self.wq &= inv_mask; captured = Some(Piece::new(PieceType::Queen, Color::White)); }
        else if self.wk & mask != 0 { self.wk &= inv_mask; captured = Some(Piece::new(PieceType::King, Color::White)); }
        else if self.bp & mask != 0 { self.bp &= inv_mask; captured = Some(Piece::new(PieceType::Pawn, Color::Black)); }
        else if self.bn & mask != 0 { self.bn &= inv_mask; captured = Some(Piece::new(PieceType::Knight, Color::Black)); }
        else if self.bb & mask != 0 { self.bb &= inv_mask; captured = Some(Piece::new(PieceType::Bishop, Color::Black)); }
        else if self.br & mask != 0 { self.br &= inv_mask; captured = Some(Piece::new(PieceType::Rook, Color::Black)); }
        else if self.bq & mask != 0 { self.bq &= inv_mask; captured = Some(Piece::new(PieceType::Queen, Color::Black)); }
        else if self.bk & mask != 0 { self.bk &= inv_mask; captured = Some(Piece::new(PieceType::King, Color::Black)); }

        // XOR out the piece from the Zobrist key if one was found
        if let Some(piece) = captured {
            *zobrist_key ^= ZOBRIST.piece(piece, sq);
        }

        captured
    }


    /// Gets the piece at a specific square index. More efficient version.
    #[inline(always)]
    fn get_piece_at(&self, sq: u8) -> Option<Piece> {
        let mask = 1u64 << sq;
        if self.occupied & mask == 0 { return None; } // Quick exit if square is empty

        if self.white_occupied & mask != 0 {
            if self.wp & mask != 0 { Some(Piece::new(PieceType::Pawn, Color::White)) }
            else if self.wn & mask != 0 { Some(Piece::new(PieceType::Knight, Color::White)) }
            else if self.wb & mask != 0 { Some(Piece::new(PieceType::Bishop, Color::White)) }
            else if self.wr & mask != 0 { Some(Piece::new(PieceType::Rook, Color::White)) }
            else if self.wq & mask != 0 { Some(Piece::new(PieceType::Queen, Color::White)) }
            else if self.wk & mask != 0 { Some(Piece::new(PieceType::King, Color::White)) }
            else { None } // Should be unreachable if occupied is correct
        } else { // Must be black occupied
            if self.bp & mask != 0 { Some(Piece::new(PieceType::Pawn, Color::Black)) }
            else if self.bn & mask != 0 { Some(Piece::new(PieceType::Knight, Color::Black)) }
            else if self.bb & mask != 0 { Some(Piece::new(PieceType::Bishop, Color::Black)) }
            else if self.br & mask != 0 { Some(Piece::new(PieceType::Rook, Color::Black)) }
            else if self.bq & mask != 0 { Some(Piece::new(PieceType::Queen, Color::Black)) }
            else if self.bk & mask != 0 { Some(Piece::new(PieceType::King, Color::Black)) }
            else { None } // Should be unreachable
        }
    }

    /// Finds the king's square index for a given color. Returns None if king is missing.
    #[inline(always)]
    fn find_king(&self, color: Color) -> Option<u8> {
        let king_board = if color == Color::White { self.wk } else { self.bk };
        if king_board == 0 { None } else { Some(king_board.trailing_zeros() as u8) }
    }

    /// Returns the occupancy bitboard for the given color.
    #[inline(always)]
    fn occupied_by_color(&self, color: Color) -> u64 {
        if color == Color::White { self.white_occupied } else { self.black_occupied }
    }

    /// Calculates the Zobrist hash key for the current state from scratch.
    /// Useful for initialization or verification.
    fn calculate_zobrist_key(&self) -> u64 {
        let mut key = 0u64;
        let zob = &*ZOBRIST; // Avoid repeated lazy_static deref

        for color_idx in 0..2 {
            let color = if color_idx == 0 { Color::White } else { Color::Black };
            for piece_idx in 0..6 {
                let piece_type = match piece_idx {
                    0 => PieceType::Pawn, 1 => PieceType::Knight, 2 => PieceType::Bishop,
                    3 => PieceType::Rook, 4 => PieceType::Queen, _ => PieceType::King,
                };
                let piece = Piece::new(piece_type, color);
                let mut board = self.get_piece_board(piece_type, color);
                while board != 0 {
                    let sq = board.trailing_zeros() as u8;
                    key ^= zob.piece(piece, sq);
                    board &= board - 1; // Clear least significant bit
                }
            }
        }

        key ^= zob.castling(self.castling_rights);
        key ^= zob.en_passant(self.en_passant_square);
        key ^= zob.side_to_move(self.turn);

        key
    }
}

// --- Event History and Stats Saving ---

#[derive(Debug, Clone, Serialize)]
struct MoveRecord {
    mv_algebraic: String, // Stores the notation used (e.g., O-O, e1g1, e7e8q)
    time_taken: Duration,
    player: Color,
    is_check: bool,
    is_checkmate: bool,
}

#[derive(Debug, Serialize, Deserialize, Clone, Copy, PartialEq, Eq)]
enum DrawReason {
    SeventyFiveMoveRule,
    FivefoldRepetition,
    InsufficientMaterial,
    TimeoutVsInsufficientMaterial,
    Stalemate,
    Agreement,
    FiftyMoveRuleClaimed,
    ThreefoldRepetitionClaimed,
}

#[derive(Debug, Clone, Serialize)]
enum GameEvent {
    Move(MoveRecord),
    OfferDraw(Color), // Records who offered
    AcceptDraw(Color), // Records who accepted
    DeclineDraw(Color), // Records who declined
    Resign(Color),
    ClaimDraw(Color, DrawReason), // Records who claimed and why
}

#[derive(Debug, Serialize)]
#[serde(tag = "type", content = "details")]
enum GameEventSummary {
    OfferDraw { player: Color },
    AcceptDraw { player: Color },
    DeclineDraw { player: Color },
    Resign { player: Color },
    ClaimDraw { player: Color, reason: DrawReason}, // Added summary for claims
}

#[derive(Debug, Serialize, Clone, Copy, PartialEq, Eq)]
enum GameResultReason {
    Checkmate { winner: Color, loser: Color },
    Timeout { winner: Color, loser: Color },
    Resignation { winner: Color, loser: Color },
    Stalemate,
    SeventyFiveMoveRule,
    FivefoldRepetition,
    InsufficientMaterial,
    TimeoutVsInsufficientMaterial,
    Agreement,
    FiftyMoveRuleClaimed,
    ThreefoldRepetitionClaimed,
}

#[derive(Debug, Serialize)]
struct GameStats {
    result: Option<GameResultReason>,
    white_final_time_remaining: Duration,
    black_final_time_remaining: Duration,
    total_game_duration_secs: u64,
    white_moves: Vec<MoveStat>,
    black_moves: Vec<MoveStat>,
    game_events: Vec<GameEventSummary>,
}

#[derive(Debug, Serialize)]
struct MoveStat {
    move_algebraic: String, // Stores the notation used
    time_taken: Duration,
    annotation: String, // +, #, or empty
}

// --- Pinned Piece Information ---
#[derive(Debug, Clone)] // Removed derive Default
struct PinInfo {
    /// Bitboard of all pieces (for the current player) that are absolutely pinned.
    pinned_pieces: u64,
    /// For each square (0-63), a bitboard representing the valid destination squares
    /// if a piece on that square is pinned. 0 if not pinned or no piece.
    /// Valid destinations include squares along the pin ray and the pinning piece itself.
    pin_restriction_map: [u64; 64],
}

// Manual implementation of Default for PinInfo (Fix for E0277)
impl Default for PinInfo {
    fn default() -> Self {
        PinInfo {
            pinned_pieces: 0,
            // Initialize the array with zeros. This works even for N > 32.
            pin_restriction_map: [0u64; 64],
        }
    }
}


// --- Game State (Added pending_draw_offer) ---
#[derive(Debug, Clone, Serialize)]
struct Game {
    current_state: BitboardState,
    #[serde(skip)]
    zobrist_key: u64,
    #[serde(skip)]
    zobrist_history: HashMap<u64, u8>, // Tracks counts of each Zobrist key seen
    event_history: Vec<GameEvent>,
    captured_white: Vec<Piece>, // Pieces captured BY White (Black pieces)
    captured_black: Vec<Piece>, // Pieces captured BY Black (White pieces)
    /// An active draw offer made by the opponent on their last turn. Cleared when current player moves/accepts/declines.
    draw_offer: Option<Color>,
    /// A draw offer made by the current player on this turn, pending their move to activate it.
    #[serde(skip)]
    pending_draw_offer: Option<Color>,
    white_time_remaining: Duration,
    black_time_remaining: Duration,
    #[serde(skip)]
    turn_start_time: Option<Instant>,
}

// Display trait for printing the board and game state
impl fmt::Display for Game {
     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let state = &self.current_state;

        // --- Captured Pieces ---
        write!(f, "Captured by White: ")?;
        let mut sorted_capt_w = self.captured_black.clone(); // White captures Black pieces
        sorted_capt_w.sort_by_key(|p| p.value());
        for piece in sorted_capt_w { write!(f, "{} ", piece)?; }
        writeln!(f)?;

        write!(f, "Captured by Black: ")?;
        let mut sorted_capt_b = self.captured_white.clone(); // Black captures White pieces
        sorted_capt_b.sort_by_key(|p| p.value());
        for piece in sorted_capt_b { write!(f, "{} ", piece)?; }
        writeln!(f)?;
        writeln!(f, "---------------------")?;

        // --- Time ---
        writeln!(f, "Black Time: {}", format_duration(self.black_time_remaining))?;
        writeln!(f, "White Time: {}", format_duration(self.white_time_remaining))?;
        writeln!(f, "---------------------")?;

        // --- Board ---
        writeln!(f, "  +-----------------+")?;
        for rank_idx in (0..8).rev() {
            write!(f, "{} | ", rank_idx + 1)?;
            for file_idx in 0..8 {
                let sq_index = (rank_idx * 8 + file_idx) as u8;
                match state.get_piece_at(sq_index) {
                    Some(piece) => write!(f, "{} ", piece)?,
                    None => write!(f, ". ")?,
                }
            }
            writeln!(f, "|")?;
        }
        writeln!(f, "  +-----------------+")?;
        writeln!(f, "    a b c d e f g h")?;

        // --- Game State Info ---
        writeln!(f, "Turn: {:?}", state.turn)?;
        writeln!(f, "Castling: W:{}{}, B:{}{}",
            if state.castling_rights.white_kingside { "K" } else { "-" },
            if state.castling_rights.white_queenside { "Q" } else { "-" },
            if state.castling_rights.black_kingside { "k" } else { "-" },
            if state.castling_rights.black_queenside { "q" } else { "-" }
        )?;
        if let Some(ep_sq) = state.en_passant_square { writeln!(f, "En Passant Target: {}", index_to_algebraic(ep_sq))?; }
        else { writeln!(f, "En Passant Target: -")?; }
        writeln!(f, "Halfmove Clock: {}", state.halfmove_clock)?;
        writeln!(f, "Fullmove Number: {}", state.fullmove_number)?;
        // writeln!(f, "Zobrist Key: {:016x}", self.zobrist_key)?; // Optional: Display Zobrist key for debugging

        // --- Annotated Move History Display ---
        let mut move_num = 1;
        let mut white_move_record: Option<&MoveRecord> = None;
        let has_moves = self.event_history.iter().any(|ev| matches!(ev, GameEvent::Move(_)));

        if has_moves {
            writeln!(f, "Move History:")?;
            for event in &self.event_history {
                if let GameEvent::Move(record) = event {
                    if record.player == Color::White {
                         // If there was a pending white move (e.g., game ended after black move), print it first
                         if let Some(wm) = white_move_record.take() {
                              let annotation = if wm.is_checkmate { "#" } else if wm.is_check { "+" } else { "" };
                              writeln!(f, "{}. {}{}", move_num, wm.mv_algebraic, annotation)?;
                              move_num += 1; // Increment move number here ONLY if white move was printed alone
                         }
                         // Store the current white move to print with black's move or at the end
                         white_move_record = Some(record);
                    } else { // Black's move
                        if let Some(wm) = white_move_record.take() { // We have a white move to pair it with
                            let white_annotation = if wm.is_checkmate { "#" } else if wm.is_check { "+" } else { "" };
                            write!(f, "{}. {}{}", move_num, wm.mv_algebraic, white_annotation)?;

                            let black_annotation = if record.is_checkmate { "#" } else if record.is_check { "+" } else { "" };
                            write!(f, " {}{}", record.mv_algebraic, black_annotation)?;
                            writeln!(f)?;
                            move_num += 1; // Increment after black's move completes the pair
                        } else {
                            // Black moved first, or white's move wasn't recorded properly. Print black move with ellipsis.
                            let black_annotation = if record.is_checkmate { "#" } else if record.is_check { "+" } else { "" };
                            // Fix: Use correct move number logic when black moves first/alone
                            write!(f, "{}. ... {}{}", move_num, record.mv_algebraic, black_annotation)?;
                            writeln!(f)?;
                            move_num += 1; // Increment even if white's move is missing
                        }
                    }
                }
            }
             // Print the last white move if the game ended after white's move
             if let Some(wm) = white_move_record {
                 let annotation = if wm.is_checkmate { "#" } else if wm.is_check { "+" } else { "" };
                 write!(f, "{}. {}{}", move_num, wm.mv_algebraic, annotation)?; // Use current move_num
                 writeln!(f)?;
            }
        }


        // --- Repetition Count (Using Zobrist History) ---
        let rep_count = self.zobrist_history.get(&self.zobrist_key).unwrap_or(&0);
        if *rep_count > 1 { writeln!(f, "Position Repetitions: {}", rep_count)?; }

        // --- Draw Offer Display ---
        // Check if there is an *active* draw offer from the opponent.
        if let Some(offering_color) = self.draw_offer {
             if offering_color == state.turn.opponent() {
                 writeln!(f, "--- {:?} has offered a draw! ('accept draw' / 'decline draw' / move) ---", offering_color)?;
             }
        }
        // Indicate if the current player has noted an offer pending their move
        else if self.pending_draw_offer == Some(state.turn) {
             writeln!(f, "--- (Draw offer noted, will be active after your move) ---")?;
        }


        Ok(())
    }
}


// --- Game Implementation ---

impl Game {
    /// Creates a new game.
    fn new() -> Self {
        let initial_time = Duration::from_secs(INITIAL_TIME_SECONDS);
        let initial_state = BitboardState::initial();
        let initial_zobrist_key = initial_state.calculate_zobrist_key();
        let mut zobrist_history = HashMap::new();
        zobrist_history.insert(initial_zobrist_key, 1);

        Game {
            current_state: initial_state,
            zobrist_key: initial_zobrist_key,
            zobrist_history,
            white_time_remaining: initial_time,
            black_time_remaining: initial_time,
            turn_start_time: Some(Instant::now()),
            event_history: Vec::new(),
            captured_white: Vec::new(),
            captured_black: Vec::new(),
            draw_offer: None, // No active offer initially
            pending_draw_offer: None, // No pending offer initially
        }
    }

    /// Restarts the turn timer.
    fn start_turn_timer(&mut self) {
        self.turn_start_time = Some(Instant::now());
    }

     // --- Bitboard Move Generation (Pseudo-Legal) ---
    /// Generates all pseudo-legal moves for the current player.
    /// Does not check for checks, pins, or castling legality beyond basic rules.
    fn generate_pseudo_legal_moves(&self, state: &BitboardState) -> Vec<Move> {
        let mut moves = Vec::with_capacity(48); // Pre-allocate reasonable capacity
        let color = state.turn;
        let opp_occupied = state.occupied_by_color(color.opponent());
        let own_occupied = state.occupied_by_color(color);
        let occupied = state.occupied; // Cache combined occupancy

        // Iterate through piece types (King and captures often first for pruning/ordering)
        for piece_type in [PieceType::King, PieceType::Pawn, PieceType::Knight, PieceType::Bishop, PieceType::Rook, PieceType::Queen] {
            let mut board = state.get_piece_board(piece_type, color);
            while board != 0 {
                let from_sq = board.trailing_zeros() as u8;
                self.generate_moves_for_piece(state, from_sq, piece_type, color, own_occupied, opp_occupied, occupied, &mut moves);
                board &= board - 1; // Clear the least significant bit
            }
        }

        // Simple Move Ordering: Put captures first (often done implicitly by generation order, but explicit sort helps)
        moves.sort_by_key(|mv| !mv.is_capture); // Sorts true (captures) before false

        moves
    }

    /// Generates pseudo-legal moves for a single piece type from a given square.
    #[inline]
    fn generate_moves_for_piece(&self, state: &BitboardState, from_sq: u8, piece_type: PieceType, color: Color, own_occupied: u64, opp_occupied: u64, occupied: u64, moves: &mut Vec<Move>) {
        match piece_type {
            PieceType::Pawn => self.generate_pawn_moves(state, from_sq, color, opp_occupied, occupied, moves),
            PieceType::Knight => self.generate_knight_moves(from_sq, own_occupied, opp_occupied, moves),
            PieceType::Bishop => self.generate_sliding_moves(from_sq, own_occupied, opp_occupied, occupied, true, false, moves),
            PieceType::Rook => self.generate_sliding_moves(from_sq, own_occupied, opp_occupied, occupied, false, true, moves),
            PieceType::Queen => self.generate_sliding_moves(from_sq, own_occupied, opp_occupied, occupied, true, true, moves),
            PieceType::King => self.generate_king_moves(state, from_sq, color, own_occupied, opp_occupied, occupied, moves),
        }
    }

     /// Generates pseudo-legal pawn moves (pushes, double pushes, captures, en passant, promotions).
     #[inline]
     fn generate_pawn_moves(&self, state: &BitboardState, from_sq: u8, color: Color, opp_occupied: u64, occupied: u64, moves: &mut Vec<Move>) {
        let from_bb = 1u64 << from_sq;
        let empty_squares = !occupied; // Use pre-calculated combined occupancy

        let (push_one_offset, push_two_offset, capture_left_offset, capture_right_offset, promotion_rank_mask, start_rank_mask, ep_capture_rank_mask) =
            if color == Color::White {
                (8i8, 16i8, 7i8, 9i8, RANK_8, RANK_2, RANK_5) // White EP capture happens *from* rank 5
            } else {
                (-8i8, -16i8, -9i8, -7i8, RANK_1, RANK_7, RANK_4) // Black EP capture happens *from* rank 4
            };

        // 1. Single Push
        let target_sq_one_signed = from_sq as i8 + push_one_offset;
        if (0..64).contains(&target_sq_one_signed) { // Check target validity
            let target_sq_one = target_sq_one_signed as u8;
            let target_bb_one = 1u64 << target_sq_one;
             if target_bb_one & empty_squares != 0 {
                // Check for Promotion
                if target_bb_one & promotion_rank_mask != 0 {
                    self.add_promotions(from_sq, target_sq_one, false, moves);
                } else {
                    moves.push(Move::new(from_sq, target_sq_one, None, false));
                }
                // 2. Double Push (only possible if single push is possible and pawn is on start rank)
                if from_bb & start_rank_mask != 0 {
                    let target_sq_two_signed = from_sq as i8 + push_two_offset;
                    // We already know target_sq_one is valid, just need to check target_sq_two
                    if (0..64).contains(&target_sq_two_signed) {
                         let target_sq_two = target_sq_two_signed as u8;
                         let target_bb_two = 1u64 << target_sq_two;
                         if target_bb_two & empty_squares != 0 {
                            moves.push(Move::new(from_sq, target_sq_two, None, false));
                        }
                    }
                }
            }
        }

        // 3. Captures (Regular and En Passant)
        for capture_offset in [capture_left_offset, capture_right_offset] {
            // Check side boundaries based on *origin* square and offset direction
            if (capture_offset == 7 || capture_offset == -9) && (from_bb & FILE_A != 0) { continue; } // Capture left from A file
            if (capture_offset == 9 || capture_offset == -7) && (from_bb & FILE_H != 0) { continue; } // Capture right from H file

            let target_sq_cap_signed = from_sq as i8 + capture_offset;
            if (0..64).contains(&target_sq_cap_signed) { // Check target validity
                let target_sq_cap = target_sq_cap_signed as u8;
                let target_bb_cap = 1u64 << target_sq_cap;
                // Regular capture
                if target_bb_cap & opp_occupied != 0 {
                    if target_bb_cap & promotion_rank_mask != 0 {
                        self.add_promotions(from_sq, target_sq_cap, true, moves);
                    } else {
                        moves.push(Move::new(from_sq, target_sq_cap, None, true));
                    }
                }
                // En Passant capture check
                // Must be on correct rank for EP capture *and* target must match EP square
                 else if (from_bb & ep_capture_rank_mask != 0) && Some(target_sq_cap) == state.en_passant_square {
                     // Mark EP as a capture (target square is empty but it's a capture event)
                     // Legality check will verify discovered check later
                     moves.push(Move::new(from_sq, target_sq_cap, None, true));
                 }
            }
        }
    }

     /// Helper to add all promotion moves for a given pawn move.
     #[inline]
     fn add_promotions(&self, from_sq: u8, to_sq: u8, is_capture: bool, moves: &mut Vec<Move>) {
        // Queen promotion is most common, add first for potential ordering benefits
        moves.push(Move::new(from_sq, to_sq, Some(PieceType::Queen), is_capture));
        moves.push(Move::new(from_sq, to_sq, Some(PieceType::Knight), is_capture)); // Common underpromotion
        moves.push(Move::new(from_sq, to_sq, Some(PieceType::Rook), is_capture));
        moves.push(Move::new(from_sq, to_sq, Some(PieceType::Bishop), is_capture));
    }

     /// Generates pseudo-legal knight moves.
     #[inline]
     fn generate_knight_moves(&self, from_sq: u8, own_occupied: u64, opp_occupied: u64, moves: &mut Vec<Move>) {
        let potential_moves = KNIGHT_ATTACKS[from_sq as usize];
        let valid_moves = potential_moves & !own_occupied; // Can land on empty or opponent square

        let mut results = valid_moves;
        while results != 0 {
            let to_sq = results.trailing_zeros() as u8;
            let is_capture = ((1u64 << to_sq) & opp_occupied) != 0;
            moves.push(Move::new(from_sq, to_sq, None, is_capture));
            results &= results - 1; // Clear the least significant bit
        }
    }

    /// Generates pseudo-legal King moves (basic moves + castling based on rights and occupancy).
    /// Legality check (moving into check, castling through check) is handled in `generate_legal_moves`.
    #[inline]
    fn generate_king_moves(&self, state: &BitboardState, from_sq: u8, color: Color, own_occupied: u64, opp_occupied: u64, occupied: u64, moves: &mut Vec<Move>) {
        let potential_moves = KING_ATTACKS[from_sq as usize];
        let valid_moves = potential_moves & !own_occupied; // Can land on empty or opponent square

        let mut results = valid_moves;
        while results != 0 {
            let to_sq = results.trailing_zeros() as u8;
            let is_capture = ((1u64 << to_sq) & opp_occupied) != 0;
            moves.push(Move::new(from_sq, to_sq, None, is_capture));
            results &= results - 1; // Clear the least significant bit
        }

        // Castling (Pseudo-legal generation: only checks rights and occupancy between king/rook)
        let (can_kside, can_qside, kside_empty_mask, qside_empty_mask, kside_rook_sq, qside_rook_sq, kside_target_sq, qside_target_sq) =
            if color == Color::White {
                (state.castling_rights.white_kingside, state.castling_rights.white_queenside,
                 (1 << 5) | (1 << 6), // f1, g1
                 (1 << 1) | (1 << 2) | (1 << 3), // b1, c1, d1
                 WHITE_KS_ROOK_START, WHITE_QS_ROOK_START,
                 WHITE_KING_KS_CASTLE_DEST, WHITE_KING_QS_CASTLE_DEST)
            } else {
                (state.castling_rights.black_kingside, state.castling_rights.black_queenside,
                 ((1 << 5) | (1 << 6)) << 56, // f8, g8
                 ((1 << 1) | (1 << 2) | (1 << 3)) << 56, // b8, c8, d8
                 BLACK_KS_ROOK_START, BLACK_QS_ROOK_START,
                 BLACK_KING_KS_CASTLE_DEST, BLACK_KING_QS_CASTLE_DEST)
            };

        let rook_board = state.get_piece_board(PieceType::Rook, color);

        // Check Kingside Castling
        if can_kside && (rook_board & (1 << kside_rook_sq) != 0) // Check if rook still exists at origin
                   && (occupied & kside_empty_mask == 0) { // Check squares king passes over are empty
            // Legality checks (king in check, path check) happen in generate_legal_moves
            moves.push(Move::new_castle(from_sq, kside_target_sq)); // Use special constructor
        }
        // Check Queenside Castling
         if can_qside && (rook_board & (1 << qside_rook_sq) != 0) // Check if rook still exists at origin
                   && (occupied & qside_empty_mask == 0) { // Check squares king passes over are empty
            // Legality checks happen later
            moves.push(Move::new_castle(from_sq, qside_target_sq)); // Use special constructor
        }
    }

    /// Generates pseudo-legal sliding piece moves (Rook, Bishop, Queen).
    #[inline]
    fn generate_sliding_moves(&self, from_sq: u8, own_occupied: u64, opp_occupied: u64, occupied: u64, diagonals: bool, orthogonals: bool, moves: &mut Vec<Move>) {
        for &(dr, df, is_diagonal) in DIRECTIONS {
            if (diagonals && is_diagonal) || (orthogonals && !is_diagonal) {
                let mut current_rank = (from_sq / 8) as i8;
                let mut current_file = (from_sq % 8) as i8;

                loop {
                    current_rank += dr;
                    current_file += df;

                    if !(0..8).contains(&current_rank) || !(0..8).contains(&current_file) { break; } // Off board

                    let next_sq = (current_rank * 8 + current_file) as u8;
                    let next_bb = 1u64 << next_sq;

                    if next_bb & own_occupied != 0 { break; } // Blocked by own piece

                    let is_capture = (next_bb & opp_occupied) != 0;
                    moves.push(Move::new(from_sq, next_sq, None, is_capture));

                    if next_bb & occupied != 0 { break; } // Stop after empty square move OR capture
                }
            }
        }
    }

     // --- Attack Generation ---
    /// Checks if a given square is attacked by the specified color.
    /// This function ignores pins and legality, just raw attack patterns.
    /// `state`: The current board state.
    /// `target_sq`: The square index (0-63) to check.
    /// `attacker_color`: The color of the pieces potentially attacking the square.
    fn is_square_attacked(&self, state: &BitboardState, target_sq: u8, attacker_color: Color) -> bool {
        let occupied = state.occupied; // Need combined occupancy for sliding pieces

        // Pawns
        let pawn_board = state.get_piece_board(PieceType::Pawn, attacker_color);
        if pawn_board != 0 { // Optimization: skip if no pawns
            let (cap_l_off, cap_r_off) = if attacker_color == Color::White {
                (-9i8, -7i8) // White pawns attack from SW (-9) and SE (-7) relative to target
            } else {
                (7i8, 9i8)   // Black pawns attack from NW (7) and NE (9) relative to target
            };

            // Check attack from potential SW/NW square
            let target_bb = 1u64 << target_sq;
            if target_bb & NOT_FILE_A != 0 { // Cannot be attacked from left if target is on A file
                let pot_att_sq_l_signed = target_sq as i8 + cap_l_off;
                 if (0..64).contains(&pot_att_sq_l_signed) { // Check bounds
                     if (pawn_board & (1u64 << pot_att_sq_l_signed)) != 0 { return true; }
                 }
            }
            // Check attack from potential SE/NE square
            if target_bb & NOT_FILE_H != 0 { // Cannot be attacked from right if target is on H file
                let pot_att_sq_r_signed = target_sq as i8 + cap_r_off;
                 if (0..64).contains(&pot_att_sq_r_signed) { // Check bounds
                     if (pawn_board & (1u64 << pot_att_sq_r_signed)) != 0 { return true; }
                 }
            }
        }

        // Knights (using precomputed table)
        let knight_board = state.get_piece_board(PieceType::Knight, attacker_color);
        if knight_board != 0 && (KNIGHT_ATTACKS[target_sq as usize] & knight_board) != 0 { return true; }

        // King (using precomputed table)
        let king_board = state.get_piece_board(PieceType::King, attacker_color);
        if king_board != 0 && (KING_ATTACKS[target_sq as usize] & king_board) != 0 { return true; }

        // Sliding Pieces (Rooks, Bishops, Queens)
        let rook_board = state.get_piece_board(PieceType::Rook, attacker_color);
        let bishop_board = state.get_piece_board(PieceType::Bishop, attacker_color);
        let queen_board = state.get_piece_board(PieceType::Queen, attacker_color);

        // Check orthogonal attacks (Rooks, Queens)
        let orth_attackers = rook_board | queen_board;
        if orth_attackers != 0 {
            let orth_attacks = self.get_sliding_attacks(target_sq, occupied, false, true);
            if orth_attacks & orth_attackers != 0 { return true; }
        }

        // Check diagonal attacks (Bishops, Queens)
        let diag_attackers = bishop_board | queen_board;
        if diag_attackers != 0 {
            let diag_attacks = self.get_sliding_attacks(target_sq, occupied, true, false);
            if diag_attacks & diag_attackers != 0 { return true; }
        }

        false // No attacker found
    }


    /// Checks if the king of the specified color is currently in check.
    #[inline]
    fn is_in_check(&self, state: &BitboardState, color: Color) -> bool {
        match state.find_king(color) {
            Some(king_sq) => self.is_square_attacked(state, king_sq, color.opponent()),
            None => {
                // This should be an unreachable state in a valid game
                // Consider panic or logging error if king is missing.
                // Returning true might be safer than false if state is corrupt.
                eprintln!("CRITICAL ERROR: King of color {:?} not found in bitboard state! State:\n{:?}", color, state);
                true
            }
        }
    }

    // --- Pin Detection ---
    /// Computes absolutely pinned pieces for the given color.
    /// Returns PinInfo containing a bitboard of pinned pieces and a restriction map.
    fn compute_pins(&self, state: &BitboardState, color: Color) -> PinInfo {
        let king_sq = match state.find_king(color) {
            Some(sq) => sq,
            None => return PinInfo::default(), // No king, no pins
        };

        let mut pin_info = PinInfo::default();
        let own_occupied = state.occupied_by_color(color);
        let opp_color = color.opponent();
        let opp_rooks_queens = state.get_piece_board(PieceType::Rook, opp_color) | state.get_piece_board(PieceType::Queen, opp_color);
        let opp_bishops_queens = state.get_piece_board(PieceType::Bishop, opp_color) | state.get_piece_board(PieceType::Queen, opp_color);
        let occupied = state.occupied;

        for &(dr, df, is_diagonal) in DIRECTIONS {
            let potential_pinners = if is_diagonal { opp_bishops_queens } else { opp_rooks_queens };
            if potential_pinners == 0 { continue; } // Optimization

            let mut ray_mask: u64 = 0; // Squares along the ray *between* king and pinner (inclusive of pinner)
            let mut potential_pinned_sq: Option<u8> = None;
            let mut current_rank = (king_sq / 8) as i8;
            let mut current_file = (king_sq % 8) as i8;

            loop {
                current_rank += dr;
                current_file += df;

                if !(0..8).contains(&current_rank) || !(0..8).contains(&current_file) { break; } // Off board
                let next_sq = (current_rank * 8 + current_file) as u8;
                let next_bb = 1u64 << next_sq;

                ray_mask |= next_bb; // Add current square to the ray

                if next_bb & occupied != 0 { // Found a piece
                    if next_bb & own_occupied != 0 { // It's a friendly piece
                        if potential_pinned_sq.is_none() {
                            potential_pinned_sq = Some(next_sq); // This *might* be pinned
                        } else {
                            // Found a second friendly piece along the ray, no pin.
                            break;
                        }
                    } else { // It's an opponent piece
                        if let Some(pinned_sq) = potential_pinned_sq { // We previously found a friendly piece
                            if next_bb & potential_pinners != 0 { // And this opponent piece is a slider of the correct type?
                                // Yes! The friendly piece is pinned.
                                pin_info.pinned_pieces |= 1u64 << pinned_sq;
                                // Restriction: can move along the ray or capture the pinner.
                                pin_info.pin_restriction_map[pinned_sq as usize] = ray_mask;
                            }
                        }
                        // Whether it was a pinner or not, stop searching along this ray.
                        break;
                    }
                }
                // Continue scanning along the ray if square was empty
            }
        }
        pin_info
    }


    // --- Legal Move Generation (Incorporating Pins and Checks) ---
    /// Generates all fully legal moves for the current player in the given state.
    fn generate_legal_moves(&self, state: &BitboardState) -> Vec<Move> {
        let mut legal_moves = Vec::with_capacity(48); // Start with reasonable capacity
        let color = state.turn;
        let opp_color = color.opponent();

        let king_sq = match state.find_king(color) {
            Some(sq) => sq,
            None => return legal_moves // Should not happen in a valid game
        };

        // 1. Compute Pins and Squares Attacked by Opponent
        let pin_info = self.compute_pins(state, color);
        let attacked_by_opponent = self.compute_attack_map(state, opp_color); // Squares attacked by ANY opponent piece

        // Check if King is currently in check
        let is_king_in_check = (attacked_by_opponent & (1u64 << king_sq)) != 0;

        // Collect pseudo-legal moves first
        let pseudo_legal_moves = self.generate_pseudo_legal_moves(state);

        for mv in pseudo_legal_moves {
            let from_bb = 1u64 << mv.from_sq;
            let moving_piece_type = state.get_piece_at(mv.from_sq).map(|p| p.kind); // Cache piece type

            // --- King Moves ---
            if moving_piece_type == Some(PieceType::King) {
                 // Regular king move legality: Cannot move into check
                 if (attacked_by_opponent & (1u64 << mv.to_sq)) != 0 { continue; }

                 // Castling legality checks
                 if mv.is_castle {
                      if is_king_in_check { continue; } // Cannot castle out of check

                      // Check squares the king passes *through*
                      let pass_sq_1;
                      if mv.to_sq > mv.from_sq { // Kingside (e.g. e1g1)
                          pass_sq_1 = mv.from_sq + 1; // f1/f8
                      } else { // Queenside (e.g. e1c1)
                          pass_sq_1 = mv.from_sq - 1; // d1/d8
                          // Need to check b1/b8 square as well for passage
                          let pass_sq_b_file = mv.from_sq - 2; // b1/b8
                          if (attacked_by_opponent & (1u64 << pass_sq_b_file)) != 0 { continue; }
                      }

                     // King cannot pass through an attacked square (d1/f1)
                     if (attacked_by_opponent & (1u64 << pass_sq_1)) != 0 { continue; }
                     // Landing square attack check already done above for all king moves

                     // Fall through if castling checks pass
                }
                // King moves (including castling that passed checks) are legal IF they don't land in check.
                // We don't need apply_move_immutable here because we already checked the destination square attack status.
                legal_moves.push(mv);
            }
            // --- Non-King Moves ---
            else {
                 // Check pin restrictions
                 let is_pinned = (from_bb & pin_info.pinned_pieces) != 0;
                 if is_pinned {
                      let allowed_move_mask = pin_info.pin_restriction_map[mv.from_sq as usize];
                      // The move's destination square must be along the pin line (or capture the pinner)
                      if ((1u64 << mv.to_sq) & allowed_move_mask) == 0 {
                          continue; // Illegal move due to pin direction
                      }
                 }

                 // En Passant - Special check needed for discovered check on EP capture
                 let is_ep_capture = moving_piece_type == Some(PieceType::Pawn) &&
                                    Some(mv.to_sq) == state.en_passant_square &&
                                    mv.is_capture && // Check capture flag set by pseudo-legal
                                    state.get_piece_at(mv.to_sq).is_none(); // Ensure target is empty

                 if is_ep_capture {
                     // Simulate the board state *after* the en passant capture
                     // Use apply_move_immutable for simulation to ensure correctness
                     match self.apply_move_immutable_no_zobrist(state, &mv) {
                         Ok((next_state, _)) => {
                             // Is the king now in check in this temporary state?
                             if !self.is_in_check(&next_state, color) {
                                 // Legal EP capture
                                 legal_moves.push(mv);
                             }
                             // else: Illegal EP capture due to discovered check, do nothing
                         },
                         Err(e) => {
                             // Should not happen if pseudo-legal was correct, but log if it does
                             eprintln!("Internal error simulating EP capture for {:?}: {}", mv.to_algebraic_string(), e);
                         }
                     }
                 } else {
                     // --- General Legality Check for Non-King, Non-EP moves ---
                     // If the king IS in check, this move must resolve it (block or capture attacker).
                     // If the king is NOT in check, this move cannot expose it (covered by pin check).
                     // The most robust check is to simulate the move and see if the king is safe afterwards.

                     // Optimization: if NOT in check AND the piece is NOT pinned, the move is guaranteed legal
                     // (as it was pseudo-legal and cannot expose the king).
                     if !is_king_in_check && !is_pinned {
                         legal_moves.push(mv);
                     } else {
                         // Must verify: does the move leave the king in check?
                         // (This covers blocking checks, pinned pieces moving along their line)
                         match self.apply_move_immutable_no_zobrist(state, &mv) {
                             Ok((next_state, _captured_piece)) => {
                                 if !self.is_in_check(&next_state, color) { // Check own king's safety
                                     legal_moves.push(mv);
                                 }
                             }
                             Err(e) => {
                                 // Should only happen with internal inconsistencies
                                 eprintln!("Internal Error during legal move generation (apply_immutable) for {:?}: {}", mv.to_algebraic_string(), e);
                             }
                         }
                     }
                 } // End !is_ep_capture block
            } // End Non-King Moves block
        } // End loop over pseudo_legal_moves

        legal_moves
    }


    /// Computes a bitboard map of all squares attacked by the given color.
    /// Used for check detection and king move validation.
    fn compute_attack_map(&self, state: &BitboardState, attacker_color: Color) -> u64 {
        let mut attack_map: u64 = 0;
        let occupied = state.occupied; // Used by sliding pieces check

        // --- Pawns ---
        let pawn_board = state.get_piece_board(PieceType::Pawn, attacker_color);
        if pawn_board != 0 {
            if attacker_color == Color::White {
                attack_map |= (pawn_board & NOT_FILE_A).wrapping_shl(7); // Attack Up-Left (NW from white pawn's perspective)
                attack_map |= (pawn_board & NOT_FILE_H).wrapping_shl(9); // Attack Up-Right (NE)
            } else { // Black
                attack_map |= (pawn_board & NOT_FILE_A).wrapping_shr(9); // Attack Down-Left (SW from black pawn's perspective)
                attack_map |= (pawn_board & NOT_FILE_H).wrapping_shr(7); // Attack Down-Right (SE)
            }
        }

        // --- Knights ---
        let knight_board = state.get_piece_board(PieceType::Knight, attacker_color);
        let mut knights = knight_board;
        while knights != 0 {
            let sq = knights.trailing_zeros() as usize;
            attack_map |= KNIGHT_ATTACKS[sq];
            knights &= knights - 1;
        }

        // --- King ---
        let king_board = state.get_piece_board(PieceType::King, attacker_color);
         if king_board != 0 {
             let sq = king_board.trailing_zeros() as usize;
             attack_map |= KING_ATTACKS[sq];
         }

        // --- Sliding Pieces (Rook, Bishop, Queen) ---
        let rook_board = state.get_piece_board(PieceType::Rook, attacker_color);
        let bishop_board = state.get_piece_board(PieceType::Bishop, attacker_color);
        let queen_board = state.get_piece_board(PieceType::Queen, attacker_color);

        // Rooks & Queens (Orthogonal)
        let mut rooks_queens = rook_board | queen_board;
        while rooks_queens != 0 {
            let sq = rooks_queens.trailing_zeros();
            attack_map |= self.get_sliding_attacks(sq as u8, occupied, false, true);
            rooks_queens &= rooks_queens - 1;
        }

        // Bishops & Queens (Diagonal)
        let mut bishops_queens = bishop_board | queen_board;
        while bishops_queens != 0 {
            let sq = bishops_queens.trailing_zeros();
            attack_map |= self.get_sliding_attacks(sq as u8, occupied, true, false);
            bishops_queens &= bishops_queens - 1;
        }

        attack_map
    }

     /// Helper for computing sliding attacks from a square, considering blockers.
     /// `occupied` should be the combined occupancy of both colors.
     #[inline]
    fn get_sliding_attacks(&self, from_sq: u8, occupied: u64, diagonals: bool, orthogonals: bool) -> u64 {
        let mut attacks: u64 = 0;

        for &(dr, df, is_diagonal) in DIRECTIONS {
            if (diagonals && is_diagonal) || (orthogonals && !is_diagonal) {
                let mut current_rank = (from_sq / 8) as i8;
                let mut current_file = (from_sq % 8) as i8;
                loop {
                    current_rank += dr;
                    current_file += df;

                    if !(0..8).contains(&current_rank) || !(0..8).contains(&current_file) { break; } // Off board
                    let next_sq = (current_rank * 8 + current_file) as u8;
                    let next_bb = 1u64 << next_sq;

                    attacks |= next_bb; // Add the square to the attack map

                    if next_bb & occupied != 0 { break; } // Stop if we hit any piece (blocker)
                }
            }
        }
        attacks
    }

    // --- Immutable Move Application (Helper for generate_legal_moves) ---
    /// Applies a move to a *copy* of the state without modifying the original game state or Zobrist key.
    /// Returns the resulting state and the captured piece (if any). Used for legality checks.
    /// IMPORTANT: Assumes the move is pseudo-legal regarding basic movement rules.
    /// Does NOT re-validate castling rights or paths beyond occupancy.
    fn apply_move_immutable_no_zobrist(&self, state: &BitboardState, mv: &Move) -> Result<(BitboardState, Option<Piece>), MoveError> {
        let mut next_state = state.clone();
        let moving_color = state.turn;
        let moving_piece = state.get_piece_at(mv.from_sq)
            .ok_or(MoveError::InternalError("Piece not found at 'from' sq in immutable apply"))?;

        // Determine capture status within this function, don't rely solely on mv.is_capture
        let is_pawn_move = moving_piece.kind == PieceType::Pawn;
        let mut castle_rook_move: Option<(u8, u8)> = None;
        let mut temp_zobrist = 0; // Dummy key, not used by caller
        let mut actual_captured_piece: Option<Piece> = None;
        let mut is_capture = false; // Start assuming no capture


        // --- Handle Castling Rook Move Pre-check ---
        if moving_piece.kind == PieceType::King && mv.is_castle {
             let (rook_from_sq, rook_to_sq) = if mv.to_sq > mv.from_sq { // Kingside
                  if moving_color == Color::White { (WHITE_KS_ROOK_START, 5) } else { (BLACK_KS_ROOK_START, 61) } // h1->f1, h8->f8
              } else { // Queenside
                 if moving_color == Color::White { (WHITE_QS_ROOK_START, 3) } else { (BLACK_QS_ROOK_START, 59) } // a1->d1, a8->d8
              };
              // Check if rook actually exists at origin in the *current* state copy
               if next_state.get_piece_at(rook_from_sq).map_or(true, |p| p.kind != PieceType::Rook || p.color != moving_color) {
                    return Err(MoveError::InternalError("Castling error: Rook missing or wrong piece at origin in immutable apply"));
               }
              castle_rook_move = Some((rook_from_sq, rook_to_sq));
        }

        // --- En Passant capture logic ---
        // Identify EP capture: pawn move, target matches EP square, target square is empty
        if is_pawn_move && Some(mv.to_sq) == state.en_passant_square && state.get_piece_at(mv.to_sq).is_none() {
             // Calculate the actual captured pawn's square
             let captured_pawn_sq = if moving_color == Color::White {
                 mv.to_sq.checked_sub(8) // Rank 6 target -> Rank 5 capture
             } else {
                 mv.to_sq.checked_add(8) // Rank 3 target -> Rank 4 capture
             };

             if let Some(cap_sq) = captured_pawn_sq {
                 if cap_sq < 64 { // Ensure valid square index
                     actual_captured_piece = next_state.clear_square(cap_sq, &mut temp_zobrist);
                     // Verify it was the correct pawn (optional sanity check)
                     if actual_captured_piece.map_or(true, |p| p.kind != PieceType::Pawn || p.color == moving_color) {
                          eprintln!("WARN (immutable): EP capture at {} expected opponent pawn at {} but found {:?}.", index_to_algebraic(mv.to_sq), index_to_algebraic(cap_sq), actual_captured_piece);
                          // If strict, return Err here
                     }
                     is_capture = true; // Mark as capture
                 } else {
                     return Err(MoveError::InternalError("Internal en passant error: Invalid capture square calculated"));
                 }
             } else {
                  return Err(MoveError::InternalError("Internal en passant error: Capture square calculation underflow/overflow"));
             }
        }

        // --- Move the main piece ---
        // 1. Clear the 'from' square (piece XOR handled by clear_square)
        next_state.clear_square(mv.from_sq, &mut temp_zobrist);
        // 2. Clear the 'to' square (handles captures, piece XOR handled by clear_square)
        let captured_on_to_sq = next_state.clear_square(mv.to_sq, &mut temp_zobrist);

        // 3. Update captured piece status (if not already set by EP)
        if captured_on_to_sq.is_some() {
            if actual_captured_piece.is_some() {
                 // This implies an EP capture where the target square was somehow occupied. Error.
                 return Err(MoveError::InternalError("Internal error: Both EP capture and direct capture detected"));
            }
             actual_captured_piece = captured_on_to_sq;
            is_capture = true; // Mark as capture
        }

        // 4. Place the piece (or promoted piece) on the 'to' square (piece XOR handled by set_piece_at)
        let piece_to_place_type = mv.promotion.unwrap_or(moving_piece.kind);
        next_state.set_piece_at(mv.to_sq, piece_to_place_type, moving_color, &mut temp_zobrist);


        // --- Handle Castling Rook Move (Piece Movement) ---
        if let Some((rook_from, rook_to)) = castle_rook_move {
            // Clear rook from origin (clear_square verified existence earlier)
            next_state.clear_square(rook_from, &mut temp_zobrist);
             // Place rook at destination
             next_state.set_piece_at(rook_to, PieceType::Rook, moving_color, &mut temp_zobrist);
        }

        // --- Update State Variables (Castling Rights, EP, Clocks, Turn) ---

        // Castling rights update
        let mut next_castling_rights = state.castling_rights;
        if moving_piece.kind == PieceType::King {
            next_castling_rights.king_moved(moving_color);
        }
        // Check if a rook moved FROM its starting square
        if moving_piece.kind == PieceType::Rook {
             match mv.from_sq {
                 WHITE_QS_ROOK_START if moving_color == Color::White => next_castling_rights.white_queenside = false,
                 WHITE_KS_ROOK_START if moving_color == Color::White => next_castling_rights.white_kingside = false,
                 BLACK_QS_ROOK_START if moving_color == Color::Black => next_castling_rights.black_queenside = false,
                 BLACK_KS_ROOK_START if moving_color == Color::Black => next_castling_rights.black_kingside = false,
                 _ => {}
             }
        }
        // Check if a rook was captured ON its starting square
        if let Some(captured) = actual_captured_piece { // Use the determined captured piece
            if captured.kind == PieceType::Rook {
                match mv.to_sq { // The square where the capture happened
                    WHITE_QS_ROOK_START => next_castling_rights.white_queenside = false,
                    WHITE_KS_ROOK_START => next_castling_rights.white_kingside = false,
                    BLACK_QS_ROOK_START => next_castling_rights.black_queenside = false,
                    BLACK_KS_ROOK_START => next_castling_rights.black_kingside = false,
                    _ => {}
                 }
            }
        }
        next_state.castling_rights = next_castling_rights;

        // En Passant square update
        next_state.en_passant_square = None; // Reset first
        if is_pawn_move {
            let rank_diff = (mv.to_sq / 8).abs_diff(mv.from_sq / 8); // Use abs_diff for safety
            if rank_diff == 2 {
                // Determine the square skipped over
                let ep_target_sq = if moving_color == Color::White { mv.from_sq + 8 } else { mv.from_sq - 8 };
                next_state.en_passant_square = Some(ep_target_sq);
            }
        }

        // Clocks update
        if is_pawn_move || is_capture { // Use the final `is_capture` status determined above
            next_state.halfmove_clock = 0;
        } else {
            next_state.halfmove_clock = state.halfmove_clock + 1;
        }
         if moving_color == Color::Black {
             next_state.fullmove_number = state.fullmove_number + 1;
         }

        // Switch turn and update final occupancy
        next_state.turn = moving_color.opponent();
        next_state.update_occupancy(); // Ensure occupancy reflects all changes

        Ok((next_state, actual_captured_piece))
    }


    /// Applies a validated legal move to the main game state, updating Zobrist key incrementally.
    /// Assumes the move is fully legal (passed generate_legal_moves) and has correct flags.
    fn apply_legal_move(&mut self, mv: &Move) -> Option<Piece> {
        let state = &mut self.current_state;
        let moving_color = state.turn;
        let moving_piece = state.get_piece_at(mv.from_sq)
            .unwrap_or_else(|| panic!("apply_legal_move called with empty 'from' square: {}", index_to_algebraic(mv.from_sq)));

        // --- Zobrist Key: XOR out previous state components ---
        let mut current_zobrist_key = self.zobrist_key;
        current_zobrist_key ^= ZOBRIST.castling(state.castling_rights);
        current_zobrist_key ^= ZOBRIST.en_passant(state.en_passant_square);
        current_zobrist_key ^= ZOBRIST.side_to_move(state.turn);

        // --- State Update ---
        // Use the move's flags directly as it's assumed to be validated
        let mut is_capture = mv.is_capture; // Use validated flag from legal move
        let is_pawn_move = moving_piece.kind == PieceType::Pawn;
        let mut castle_rook_move: Option<(u8, u8)> = None;
        let mut actual_captured_piece: Option<Piece> = None;

        // --- King Move & Castling Rights Update ---
        if moving_piece.kind == PieceType::King {
             if mv.is_castle {
                 let (rook_from_sq, rook_to_sq) = if mv.to_sq > mv.from_sq { // Kingside
                      if moving_color == Color::White { (WHITE_KS_ROOK_START, 5) } else { (BLACK_KS_ROOK_START, 61) }
                  } else { // Queenside
                     if moving_color == Color::White { (WHITE_QS_ROOK_START, 3) } else { (BLACK_QS_ROOK_START, 59) }
                  };
                  castle_rook_move = Some((rook_from_sq, rook_to_sq));
             }
             // Update castling rights *state* (Zobrist handled separately)
             state.castling_rights.king_moved(moving_color);
        }

        // --- En Passant Capture ---
        let current_ep_square = state.en_passant_square; // Cache before state change
        // Check based on validated move flags and state
        if is_pawn_move && mv.is_capture && Some(mv.to_sq) == current_ep_square && state.get_piece_at(mv.to_sq).is_none() {
            let captured_pawn_sq = if moving_color == Color::White { mv.to_sq.wrapping_sub(8) } else { mv.to_sq.wrapping_add(8) };
             if captured_pawn_sq < 64 {
                 // Clear captured pawn (Zobrist update happens inside clear_square)
                 actual_captured_piece = state.clear_square(captured_pawn_sq, &mut current_zobrist_key);
                 if actual_captured_piece.map_or(true, |p| p.kind != PieceType::Pawn || p.color == moving_color) {
                      eprintln!("WARN (apply_legal): EP capture at {} expected opponent pawn at {} but found {:?}.", index_to_algebraic(mv.to_sq), index_to_algebraic(captured_pawn_sq), actual_captured_piece);
                 }
                 // is_capture flag from mv should already be true
             } else {
                  panic!("CRITICAL (apply_legal): Invalid EP capture square calculated: {}", captured_pawn_sq);
             }
        }

        // --- Move the main piece ---
        // 1. Clear 'from' sq (Zobrist done inside)
        state.clear_square(mv.from_sq, &mut current_zobrist_key);
        // 2. Clear 'to' sq (handles captures, Zobrist done inside)
        let captured_on_to_sq = state.clear_square(mv.to_sq, &mut current_zobrist_key);
        if captured_on_to_sq.is_some() {
            if actual_captured_piece.is_some() {
                // This implies EP happened AND target was occupied - should be impossible if move was legal
                panic!("CRITICAL (apply_legal): Both EP capture and direct capture detected for legal move {}", mv.to_algebraic_string());
            }
            actual_captured_piece = captured_on_to_sq;
            // is_capture should already be true if mv was correct
            if !is_capture {
                eprintln!("WARN (apply_legal): Move {:?} had direct capture but is_capture flag was false.", mv);
                is_capture = true; // Correct the flag state if needed
            }
        }
        // 3. Place piece/promotion on 'to' sq (Zobrist done inside)
        let piece_to_place_type = mv.promotion.unwrap_or(moving_piece.kind);
        state.set_piece_at(mv.to_sq, piece_to_place_type, moving_color, &mut current_zobrist_key);

        // --- Handle Castling Rook Move (Piece Movement & Zobrist) ---
        if let Some((rook_from, rook_to)) = castle_rook_move {
             // Clear rook from origin (Zobrist done inside)
             state.clear_square(rook_from, &mut current_zobrist_key);
             // Place rook at destination (Zobrist done inside)
             state.set_piece_at(rook_to, PieceType::Rook, moving_color, &mut current_zobrist_key);
        }

        // --- Update State Variables (Castling Rights, EP, Clocks, Turn) ---

        // Update castling rights state based on rook moves/captures (if not already updated by king move)
        // Check if rook moved FROM start square
        if moving_piece.kind == PieceType::Rook {
             match mv.from_sq {
                 WHITE_QS_ROOK_START if moving_color == Color::White => state.castling_rights.white_queenside = false,
                 WHITE_KS_ROOK_START if moving_color == Color::White => state.castling_rights.white_kingside = false,
                 BLACK_QS_ROOK_START if moving_color == Color::Black => state.castling_rights.black_queenside = false,
                 BLACK_KS_ROOK_START if moving_color == Color::Black => state.castling_rights.black_kingside = false,
                 _ => {}
             }
        }
        // Check if rook was captured ON start square
        if let Some(captured) = actual_captured_piece { // Use the piece determined earlier
            if captured.kind == PieceType::Rook {
                 match mv.to_sq { // Capture happens at the 'to' square
                     WHITE_QS_ROOK_START => state.castling_rights.white_queenside = false,
                     WHITE_KS_ROOK_START => state.castling_rights.white_kingside = false,
                     BLACK_QS_ROOK_START => state.castling_rights.black_queenside = false,
                     BLACK_KS_ROOK_START => state.castling_rights.black_kingside = false,
                     _ => {}
                 }
             }
        }

        // En Passant square update
        state.en_passant_square = None; // Reset first
        if is_pawn_move {
            let rank_diff = (mv.to_sq / 8).abs_diff(mv.from_sq / 8);
            if rank_diff == 2 { // Double push creates new EP target
                let ep_target_sq = if moving_color == Color::White { mv.from_sq + 8 } else { mv.from_sq - 8 };
                state.en_passant_square = Some(ep_target_sq);
            }
        }

        // Clocks update
        if is_pawn_move || is_capture { // Use the potentially corrected `is_capture` status
            state.halfmove_clock = 0;
        } else {
            state.halfmove_clock += 1;
        }
        if moving_color == Color::Black {
            state.fullmove_number += 1;
        }

        // Switch turn
        state.turn = moving_color.opponent();

        // --- Zobrist Key: XOR in new state components ---
        current_zobrist_key ^= ZOBRIST.castling(state.castling_rights); // XOR in *new* castling rights
        current_zobrist_key ^= ZOBRIST.en_passant(state.en_passant_square); // XOR in *new* EP square
        current_zobrist_key ^= ZOBRIST.side_to_move(state.turn); // XOR in *new* side to move

        // Update occupancy (critical AFTER all piece movements)
        state.update_occupancy();

        // --- Finalize Zobrist Key ---
        self.zobrist_key = current_zobrist_key;

        // Return the piece that was actually captured (could be None)
        actual_captured_piece
    }


    // --- Public Move Execution Interface ---
    /// Attempts to make a move provided by the user (after parsing).
    /// Validates the move against legal moves, handles promotions, updates game state.
    pub fn make_legal_move(&mut self, mv: &Move) -> Result<(), MoveError> {
        // 1. Find the corresponding legal move
        // Generate legal moves for the current state
        let legal_moves = self.generate_legal_moves(&self.current_state);

        // Find the *exact* legal move matching the input (including promotion)
        let found_legal_move = legal_moves.iter().find(|&legal_mv|
            legal_mv.from_sq == mv.from_sq &&
            legal_mv.to_sq == mv.to_sq &&
            legal_mv.promotion == mv.promotion // Promotion must match!
        );

        // 2. Handle Illegal Move Attempt
        if found_legal_move.is_none() {
            // Provide specific error feedback
            let from_piece = self.current_state.get_piece_at(mv.from_sq);
            if from_piece.is_none() {
                return Err(MoveError::PieceNotFound(mv.from_sq));
            }
            if from_piece.map_or(true, |p| p.color != self.current_state.turn) {
                return Err(MoveError::NotPlayersTurn);
            }
            // Check if the basic move pattern exists but leaves king in check
             match self.apply_move_immutable_no_zobrist(&self.current_state, mv) {
                 Ok((next_state, _)) => {
                     if self.is_in_check(&next_state, self.current_state.turn) {
                         return Err(MoveError::LeavesKingInCheck(mv.to_algebraic_string()));
                     } else {
                         // If it doesn't leave king in check, but wasn't in legal_moves,
                         // it must be an illegal pattern (e.g., bad castle, blocked path)
                         // Check if *any* pseudo-legal move existed with this from/to/promo
                         // to differentiate between "bad pattern" and "rule violation like check/pin"
                         let pseudo_exists = self.generate_pseudo_legal_moves(&self.current_state).iter().any(|ps_mv|
                            ps_mv.from_sq == mv.from_sq && ps_mv.to_sq == mv.to_sq && ps_mv.promotion == mv.promotion
                         );
                         if pseudo_exists {
                             // It was pseudo-legal but failed the full legality check (likely pin or similar)
                             return Err(MoveError::IllegalMovePattern(format!("{} (violates rules like pins)", mv.to_algebraic_string())));
                         } else {
                            // Basic move pattern itself wasn't even pseudo-legal
                            return Err(MoveError::IllegalMovePattern(format!("{} (invalid piece movement)", mv.to_algebraic_string())));
                         }
                     }
                 },
                 Err(MoveError::InternalError(e)) => {
                    // If immutable apply failed due to internal logic (e.g. bad castle params from input)
                    eprintln!("Internal error check failed for {}: {}", mv.to_algebraic_string(), e);
                    return Err(MoveError::IllegalMovePattern(mv.to_algebraic_string()));
                 }
                 Err(other_err) => {
                    // Other specific errors from immutable apply could be returned
                    return Err(other_err);
                 }
             }
        }

        // --- If move is legal ---
        let player_color = self.current_state.turn; // Color of the player making the move
        let legal_move_to_apply = found_legal_move.unwrap().clone(); // Clone the validated legal move

        // 3. Activate Pending Draw Offer / Clear Active Offer
        if self.pending_draw_offer == Some(player_color) {
            self.draw_offer = self.pending_draw_offer.take(); // Move pending to active
        } else {
             self.draw_offer = None; // Making a move clears any active opponent offer
        }
        self.pending_draw_offer = None; // Always clear pending offer after move attempt


        // 4. Record Time Spent
        let time_spent = self.turn_start_time
            .map(|start_time| Instant::now().saturating_duration_since(start_time))
            .unwrap_or(Duration::ZERO);
        let current_player_time_mut = match player_color {
            Color::White => &mut self.white_time_remaining,
            Color::Black => &mut self.black_time_remaining,
        };
        *current_player_time_mut = current_player_time_mut.saturating_sub(time_spent);


        // 5. Apply the Legal Move to the main state
        let captured_piece_opt = self.apply_legal_move(&legal_move_to_apply);

         // 6. Update captured pieces list
         if let Some(captured) = captured_piece_opt {
              match player_color {
                  Color::White => self.captured_black.push(captured), // White captures Black pieces
                  Color::Black => self.captured_white.push(captured), // Black captures White pieces
              }
         }

        // 7. Update Zobrist History Count
        let count = self.zobrist_history.entry(self.zobrist_key).or_insert(0);
        *count += 1;

        // 8. Check for Check / Checkmate *after* the move
        let opponent_color = self.current_state.turn; // Turn has now switched
        let is_check = self.is_in_check(&self.current_state, opponent_color);
        // Checkmate check requires generating opponent's moves in the *new* state
        let opponent_legal_moves = self.generate_legal_moves(&self.current_state);
        let opponent_has_moves = !opponent_legal_moves.is_empty();
        let is_checkmate = is_check && !opponent_has_moves;

        // 9. Record Move Event
        let record = MoveRecord {
            mv_algebraic: legal_move_to_apply.to_algebraic_string(), // Use the applied move's notation
            time_taken: time_spent,
            player: player_color, // The player who made the move
            is_check,             // Is the *opponent* now in check?
            is_checkmate,         // Is the *opponent* now checkmated?
        };
        self.event_history.push(GameEvent::Move(record));

        // 10. Start Timer for the next player
        self.start_turn_timer();
        Ok(())
    }


    // --- Insufficient Material Logic (Enhanced) ---
     /// Checks for draw by insufficient material based on FIDE rules (Art. 5.2.2).
     /// This checks for positions where checkmate is impossible by any sequence of legal moves.
     fn is_insufficient_material(&self) -> bool {
         let state = &self.current_state;

        // Rule out positions with pawns, rooks, or queens immediately, as mate is always possible.
        if state.wp != 0 || state.bp != 0 || state.wr != 0 || state.br != 0 || state.wq != 0 || state.bq != 0 { return false; }

        let white_knights = state.wn.count_ones();
        let black_knights = state.bn.count_ones();
        let white_bishops = state.wb.count_ones();
        let black_bishops = state.bb.count_ones();

        let white_piece_count = white_knights + white_bishops;
        let black_piece_count = black_knights + black_bishops;

        // Case 1: King vs King
        if white_piece_count == 0 && black_piece_count == 0 { return true; }

        // Case 2: King vs King + Minor Piece (Knight or Bishop)
        if (white_piece_count == 0 && black_piece_count == 1) ||
           (black_piece_count == 0 && white_piece_count == 1) { return true; }

        // Case 3: King + Bishop(s) vs King + Bishop(s) - ALL bishops on the same color squares
        if white_knights == 0 && black_knights == 0 && white_piece_count > 0 && black_piece_count > 0 { // Both sides have only bishops
            let all_bishops = state.wb | state.bb;
            // Standard dark/light square masks
            const DARK_SQUARES : u64 = 0xAA55AA55AA55AA55;
            const LIGHT_SQUARES: u64 = !DARK_SQUARES;

            // Check if all bishops are on dark squares OR all bishops are on light squares
            if (all_bishops & LIGHT_SQUARES == 0) || (all_bishops & DARK_SQUARES == 0) {
                return true;
            }
        }

        // If none of the above draw conditions are met, assume material is sufficient.
        false
    }

    /// Checks if a side has *any* material capable of delivering checkmate *if unopposed*.
    /// Used for timeout rules (Timeout vs Insufficient Material - FIDE Art. 6.9).
    /// The player who ran out of time loses *unless* the opponent cannot possibly checkmate.
    fn has_sufficient_mating_material(&self, color: Color) -> bool {
        let state = &self.current_state;
        if color == Color::White {
             // Pawns, Rooks, or Queens can always mate.
             if state.wp != 0 || state.wr != 0 || state.wq != 0 { return true; }
             // Two knights can force mate (though difficult).
             if state.wn.count_ones() >= 2 { return true; }
             // Two bishops can force mate (if on different colors, checked implicitly by count >= 2).
             if state.wb.count_ones() >= 2 { return true; }
             // Bishop and Knight can force mate.
             if state.wn.count_ones() >= 1 && state.wb.count_ones() >= 1 { return true; }
        } else { // Black
             if state.bp != 0 || state.br != 0 || state.bq != 0 { return true; }
             if state.bn.count_ones() >= 2 { return true; }
             if state.bb.count_ones() >= 2 { return true; }
             if state.bn.count_ones() >= 1 && state.bb.count_ones() >= 1 { return true; }
        }
        // Otherwise (lone King, K+N, K+B), cannot force mate against a lone King.
        false
    }


    // --- Game Termination Status Check ---
    /// Checks for automatic game end conditions (checkmate, stalemate, automatic draws, timeout).
    pub fn check_automatic_game_end(&self) -> Option<GameResult> {
        let state = &self.current_state;
        let current_player = state.turn;
        let opponent = current_player.opponent();

        // 1. Timeout check (Must check this first)
        if self.white_time_remaining == Duration::ZERO {
            // White ran out of time. Black wins UNLESS Black cannot possibly checkmate.
            return Some(if self.has_sufficient_mating_material(Color::Black)
                { GameResult::Win(Color::Black, WinReason::Timeout) }
                else { GameResult::Draw(DrawReason::TimeoutVsInsufficientMaterial) });
        }
        if self.black_time_remaining == Duration::ZERO {
            // Black ran out of time. White wins UNLESS White cannot possibly checkmate.
            return Some(if self.has_sufficient_mating_material(Color::White)
                { GameResult::Win(Color::White, WinReason::Timeout) }
                else { GameResult::Draw(DrawReason::TimeoutVsInsufficientMaterial) });
        }

        // 2. Checkmate / Stalemate check (Needs to be done before automatic draws involving position repetition or 50-move)
        // Generate legal moves for the player whose turn it is.
        let legal_moves = self.generate_legal_moves(state);
        if legal_moves.is_empty() {
            // Check if the current player is in check
            return Some(if self.is_in_check(state, current_player)
                { GameResult::Win(opponent, WinReason::Checkmate) } // Current player is checkmated
                else { GameResult::Draw(DrawReason::Stalemate) }); // Current player is stalemated
        }

        // 3. Automatic Draw Rules (FIDE Article 9.6 & 5.2.2) - Check *after* move legality/stalemate/checkmate
        // 75-move rule (Art. 9.6.2): 75 moves by each player without pawn move or capture (150 half-moves)
        if state.halfmove_clock >= 150 { return Some(GameResult::Draw(DrawReason::SeventyFiveMoveRule)); }
        // Fivefold repetition (Art. 9.6.1): Same position occurs 5 times
        if *self.zobrist_history.get(&self.zobrist_key).unwrap_or(&0) >= 5 { return Some(GameResult::Draw(DrawReason::FivefoldRepetition)); }
        // Insufficient material (Art. 5.2.2): Checkmate is impossible
        if self.is_insufficient_material() { return Some(GameResult::Draw(DrawReason::InsufficientMaterial)); }


        // 4. No automatic end condition met
        None
    }

    // --- Action Handlers (Draw Logic, Resign, Claim) ---

    /// Notes a draw offer from the current player. Does not pass the turn or activate the offer yet.
    pub fn offer_draw(&mut self) -> Result<(), CommandError> {
        let offering_player = self.current_state.turn;

        // Cannot offer if opponent has an active offer pending acceptance/rejection
        if self.draw_offer == Some(offering_player.opponent()) {
             return Err(CommandError::OpponentDrawOfferPending);
        }
        // Cannot offer if already noted a pending offer this turn
        if self.pending_draw_offer == Some(offering_player) {
             return Err(CommandError::DrawAlreadyOffered);
        }

        // Note the pending offer
        self.pending_draw_offer = Some(offering_player);
        // Record the event immediately
        self.event_history.push(GameEvent::OfferDraw(offering_player));
        Ok(())
    }

    /// Accepts an *active* draw offer made by the opponent. Ends the game.
    pub fn accept_draw(&mut self) -> Result<GameResult, CommandError> {
         let accepting_player = self.current_state.turn;
         // Check if there is an *active* offer from the opponent.
         if self.draw_offer == Some(accepting_player.opponent()) {
            println!("--- {:?} accepts the draw offer. ---", accepting_player);
            self.draw_offer = None; // Clear the active offer
            self.pending_draw_offer = None; // Clear any pending offer too (safety)
            self.event_history.push(GameEvent::AcceptDraw(accepting_player));
            Ok(GameResult::Draw(DrawReason::Agreement)) // Return result to end game
        } else {
             // Can't accept own offer or if no offer exists
             if self.draw_offer == Some(accepting_player) || self.pending_draw_offer == Some(accepting_player) {
                 Err(CommandError::CannotAcceptOwnDrawOffer)
             } else {
                 Err(CommandError::NoDrawToAccept)
             }
        }
    }

    /// Explicitly declines an *active* draw offer made by the opponent.
    /// Turn remains with the player who declined.
    pub fn decline_draw(&mut self) -> Result<(), CommandError> {
         let declining_player = self.current_state.turn;
        // Check if there is an *active* offer from the opponent
        if self.draw_offer == Some(declining_player.opponent()) {
            println!("--- {:?} declines the draw offer. ---", declining_player);
            self.draw_offer = None; // Clear the active offer
            self.pending_draw_offer = None; // Clear any pending offer too (safety)
            self.event_history.push(GameEvent::DeclineDraw(declining_player));
            Ok(())
         } else {
             // Can't decline own offer or if no offer exists
             if self.draw_offer == Some(declining_player) || self.pending_draw_offer == Some(declining_player) {
                 Err(CommandError::CannotDeclineOwnDrawOffer)
             } else {
                 Err(CommandError::NoDrawToDecline)
             }
         }
    }

    /// Resigns the game. Ends the game.
    pub fn resign(&mut self) -> GameResult {
        let resigning_player = self.current_state.turn;
        println!("--- {:?} resigns. ---", resigning_player);
        self.event_history.push(GameEvent::Resign(resigning_player));
        // Clear any offers on resignation
        self.draw_offer = None;
        self.pending_draw_offer = None;
        GameResult::Win(resigning_player.opponent(), WinReason::Resignation)
    }

    /// Claims a draw based on 50-move or threefold repetition rules for the *current* position.
    /// Ends the game if claim is valid (FIDE Article 9.2, 9.3).
    pub fn claim_draw(&mut self) -> Result<GameResult, CommandError> {
        let claiming_player = self.current_state.turn;

        // Check 50-move rule claim (Art 9.3): Player can claim if the last 50 moves by each side
        // contained no pawn move or capture. This means the halfmove clock is >= 100.
        if self.current_state.halfmove_clock >= 100 {
            let reason = DrawReason::FiftyMoveRuleClaimed;
            println!("--- {:?} claims draw by 50-move rule. ---", claiming_player);
            self.event_history.push(GameEvent::ClaimDraw(claiming_player, reason));
            self.draw_offer = None; self.pending_draw_offer = None; // Clear offers
            return Ok(GameResult::Draw(reason));
        }
        // Check 3-fold repetition claim (Art 9.2): Player can claim if the *same position* has
        // just appeared for the third time (or is about to appear).
        // We check if the *current* position count is already 3 or more.
        if *self.zobrist_history.get(&self.zobrist_key).unwrap_or(&0) >= 3 {
             let reason = DrawReason::ThreefoldRepetitionClaimed;
             println!("--- {:?} claims draw by threefold repetition. ---", claiming_player);
             self.event_history.push(GameEvent::ClaimDraw(claiming_player, reason));
             self.draw_offer = None; self.pending_draw_offer = None; // Clear offers
             return Ok(GameResult::Draw(reason));
        }

        // If neither condition met for the current board state
        Err(CommandError::DrawClaimInvalid)
    }


    // --- Stats Generation and Saving ---
    /// Generates statistics for the completed or current game state.
    fn generate_stats(&self, final_result: Option<GameResult>) -> GameStats {
        let mut white_moves_stats = Vec::new();
        let mut black_moves_stats = Vec::new();
        let mut game_events_summary = Vec::new();
        let mut total_duration = Duration::ZERO;

        for event in &self.event_history {
            match event {
                GameEvent::Move(record) => {
                    let annotation = if record.is_checkmate { "#".to_string() }
                                     else if record.is_check { "+".to_string() }
                                     else { String::new() };
                    let move_stat = MoveStat {
                        move_algebraic: record.mv_algebraic.clone(),
                        time_taken: record.time_taken,
                        annotation,
                    };
                    match record.player {
                        Color::White => white_moves_stats.push(move_stat),
                        Color::Black => black_moves_stats.push(move_stat),
                    }
                    total_duration += record.time_taken;
                },
                GameEvent::OfferDraw(player) => { game_events_summary.push(GameEventSummary::OfferDraw { player: *player }); },
                GameEvent::AcceptDraw(player) => { game_events_summary.push(GameEventSummary::AcceptDraw { player: *player }); },
                GameEvent::DeclineDraw(player) => { game_events_summary.push(GameEventSummary::DeclineDraw { player: *player }); },
                GameEvent::Resign(player) => { game_events_summary.push(GameEventSummary::Resign { player: *player }); },
                GameEvent::ClaimDraw(player, reason) => { game_events_summary.push(GameEventSummary::ClaimDraw{player: *player, reason: *reason }); }
            }
        }

        // Convert internal GameResult/Reason to serializable GameResultReason
        let result_reason = final_result.map(|res| match res {
            GameResult::Win(winner, reason) => match reason {
                WinReason::Checkmate => GameResultReason::Checkmate { winner, loser: winner.opponent() },
                WinReason::Timeout => GameResultReason::Timeout { winner, loser: winner.opponent() },
                WinReason::Resignation => GameResultReason::Resignation { winner, loser: winner.opponent() },
            },
            GameResult::Draw(reason) => match reason {
                DrawReason::Stalemate => GameResultReason::Stalemate,
                DrawReason::SeventyFiveMoveRule => GameResultReason::SeventyFiveMoveRule,
                DrawReason::FivefoldRepetition => GameResultReason::FivefoldRepetition,
                DrawReason::InsufficientMaterial => GameResultReason::InsufficientMaterial,
                DrawReason::TimeoutVsInsufficientMaterial => GameResultReason::TimeoutVsInsufficientMaterial,
                DrawReason::Agreement => GameResultReason::Agreement,
                DrawReason::FiftyMoveRuleClaimed => GameResultReason::FiftyMoveRuleClaimed,
                DrawReason::ThreefoldRepetitionClaimed => GameResultReason::ThreefoldRepetitionClaimed,
            },
        });

        // Ensure final time remaining isn't negative (should be handled by saturating_sub)
        let white_final_time = self.white_time_remaining;
        let black_final_time = self.black_time_remaining;


        GameStats {
            result: result_reason,
            white_final_time_remaining: white_final_time,
            black_final_time_remaining: black_final_time,
            total_game_duration_secs: total_duration.as_secs(), // Approximate duration from move times
            white_moves: white_moves_stats,
            black_moves: black_moves_stats,
            game_events: game_events_summary,
        }
    }

    /// Saves the generated game statistics to a JSON file.
    pub fn save_stats_to_file(&self, filename: &str, final_result: Option<GameResult>) -> Result<(), SaveLoadError> {
        let stats = self.generate_stats(final_result);

        let json_data = serde_json::to_string_pretty(&stats)
            .map_err(SaveLoadError::Serialization)?;

        fs::write(filename, json_data)
            .map_err(|e| SaveLoadError::Io(filename.to_string(), e))?;

        Ok(())
    }

} // End impl Game

// --- Custom Error Types ---

#[derive(Debug)]
pub enum MoveError {
    InvalidFormat(String),
    PieceNotFound(u8),
    NotPlayersTurn,
    LeavesKingInCheck(String),
    IllegalMovePattern(String), // Covers pins, invalid castle paths, blockages etc.
    InvalidPromotion(String),
    InternalError(&'static str), // For logic errors within the engine
}
impl fmt::Display for MoveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MoveError::InvalidFormat(input) => write!(f, "Invalid move format: '{}'. Use format like 'e2e4', 'O-O', 'O-O-O' or 'a7a8q'.", input),
            MoveError::PieceNotFound(sq) => write!(f, "No piece found at {}", index_to_algebraic(*sq)),
            MoveError::NotPlayersTurn => write!(f, "It's not that piece's turn to move."),
            MoveError::LeavesKingInCheck(mv) => write!(f, "Illegal move '{}': Leaves king in check.", mv),
            MoveError::IllegalMovePattern(mv) => write!(f, "Illegal move pattern or violates game rules: '{}'", mv),
            MoveError::InvalidPromotion(reason) => write!(f, "Invalid promotion: {}", reason),
            MoveError::InternalError(reason) => write!(f, "Internal move logic error: {}", reason),
        }
    }
}
impl Error for MoveError {}

#[derive(Debug)]
pub enum CommandError {
    UnknownCommand(String),
    MissingArgument(String),
    InvalidArgument(String),
    SaveLoadError(SaveLoadError),
    DrawAlreadyOffered, // When trying to offer again in the same turn
    NoDrawToAccept,
    NoDrawToDecline,
    OpponentDrawOfferPending, // Can't offer if opponent already did
    DrawClaimInvalid,         // Conditions for 50-move/3-fold not met
    CannotAcceptOwnDrawOffer,
    CannotDeclineOwnDrawOffer,
    IoError(io::Error),       // General IO Error for input handling
}
impl fmt::Display for CommandError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CommandError::UnknownCommand(cmd) => write!(f, "Unknown command: '{}'. Type 'help' for commands.", cmd),
            CommandError::MissingArgument(cmd) => write!(f, "Missing argument for command: '{}'", cmd),
            CommandError::InvalidArgument(arg) => write!(f, "Invalid argument: '{}'", arg),
            CommandError::SaveLoadError(e) => write!(f, "Stats Save Error: {}", e),
            CommandError::DrawAlreadyOffered => write!(f, "You have already noted a draw offer this turn. Please make your move."),
            CommandError::NoDrawToAccept => write!(f, "No active draw offer from opponent to accept."),
            CommandError::NoDrawToDecline => write!(f, "No active draw offer from opponent to decline."),
            CommandError::OpponentDrawOfferPending => write!(f, "Cannot offer draw, opponent has an active offer pending."),
            CommandError::DrawClaimInvalid => write!(f, "Conditions for claiming a draw (50-move or 3-fold repetition) are not met for the current position."),
            CommandError::CannotAcceptOwnDrawOffer => write!(f, "You cannot accept your own draw offer."),
            CommandError::CannotDeclineOwnDrawOffer => write!(f, "You cannot decline your own draw offer."),
            CommandError::IoError(e) => write!(f, "Input/Output error: {}", e),
        }
    }
}
impl Error for CommandError {}

// Automatic conversions for convenience
impl From<SaveLoadError> for CommandError {
    fn from(e: SaveLoadError) -> Self { CommandError::SaveLoadError(e) }
}
impl From<io::Error> for CommandError {
    fn from(e: io::Error) -> Self { CommandError::IoError(e) }
}
impl From<MoveError> for CommandError {
    fn from(e: MoveError) -> Self {
        // Convert move errors that arise during command parsing/execution
        match e {
            MoveError::InvalidFormat(s) => CommandError::InvalidArgument(format!("Invalid move format used in command/input: {}", s)),
            MoveError::InvalidPromotion(s) => CommandError::InvalidArgument(format!("Invalid promotion used in command/input: {}", s)),
            // Other move errors might indicate logic flaws if they reach command handling
            _ => CommandError::InvalidArgument(format!("Underlying move error: {}", e)),
        }
    }
}


#[derive(Debug)]
pub enum SaveLoadError {
    Serialization(serde_json::Error),
    Io(String, io::Error),
}
impl fmt::Display for SaveLoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SaveLoadError::Serialization(e) => write!(f, "Serialization error: {}", e),
            SaveLoadError::Io(file, e) => write!(f, "I/O error with file '{}': {}", file, e),
        }
    }
}
impl Error for SaveLoadError {}


// --- Game Result Enums (Internal Representation) ---

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum GameResult {
    Win(Color, WinReason),
    Draw(DrawReason), // Use the shared DrawReason enum
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
enum WinReason { Checkmate, Timeout, Resignation }

// --- Input Parsing ---

// Updated UserInput enum
#[derive(Debug)]
enum UserInput {
    Move(Move), // Represents a standard move attempt (e.g., e2e4, a7a8q)
    Command(Command),
    CastleKingside,
    CastleQueenside,
}

#[derive(Debug)]
enum Command {
    OfferDraw, AcceptDraw, DeclineDraw,
    Resign, History, ClaimDraw, Help, Quit,
    SaveStats(String),
}

/// Parses user input string into a UserInput variant or returns a CommandError.
fn parse_user_input(input: &str) -> Result<UserInput, CommandError> {
    let trimmed_input = input.trim();
    let lower_input = trimmed_input.to_lowercase();

    // Check for special notation first
    match lower_input.as_str() {
        "o-o" | "0-0" => return Ok(UserInput::CastleKingside),
        "o-o-o" | "0-0-0" => return Ok(UserInput::CastleQueenside),
        _ => {} // Continue parsing if not castling notation
    }

    // Check for commands (split once for efficiency)
    let mut parts = trimmed_input.splitn(2, char::is_whitespace);
    let command_word = parts.next().unwrap_or("").to_lowercase(); // Handle empty input gracefully
    let argument = parts.next().unwrap_or("").trim(); // Remainder is argument, trim whitespace

    match command_word.as_str() {
        "offer" if argument == "draw" => return Ok(UserInput::Command(Command::OfferDraw)),
        "accept" if argument == "draw" => return Ok(UserInput::Command(Command::AcceptDraw)),
        "decline" if argument == "draw" => return Ok(UserInput::Command(Command::DeclineDraw)),
        "claim" if argument == "draw" => return Ok(UserInput::Command(Command::ClaimDraw)),
        "resign" => return Ok(UserInput::Command(Command::Resign)),
        "history" => return Ok(UserInput::Command(Command::History)),
        "help" | "?" => return Ok(UserInput::Command(Command::Help)),
        "quit" | "exit" => return Ok(UserInput::Command(Command::Quit)),
        "savestats" => {
            let filename = if argument.is_empty() { DEFAULT_STATS_FILENAME } else { argument }.to_string();
            return Ok(UserInput::Command(Command::SaveStats(filename)));
        }
        _ => {} // Not a recognized command word, try parsing as a move
    }

    // Attempt to parse as a standard algebraic move (e.g., e2e4, a7a8q)
    parse_move_algebraic(trimmed_input)
        .map(UserInput::Move)
        // Convert MoveError to CommandError for consistent error handling in main loop
        .map_err(|move_err| CommandError::InvalidArgument(
            format!("Invalid input '{}': {}", trimmed_input, move_err))
        )
}


/// Parses a string in algebraic notation (e.g., "e2e4", "a7a8q") into a Move struct.
/// Does NOT handle castling notation (O-O, O-O-O).
/// Does NOT validate legality, only format. `is_capture`/`is_castle` flags are initially false.
fn parse_move_algebraic(input: &str) -> Result<Move, MoveError> {
    let trimmed = input.trim();
    if !(4..=5).contains(&trimmed.len()) {
        return Err(MoveError::InvalidFormat(trimmed.to_string()));
    }

    let from_str = &trimmed[0..2];
    let to_str = &trimmed[2..4];

    let from_sq = algebraic_to_index(from_str)
                    .ok_or_else(|| MoveError::InvalidFormat(format!("Invalid 'from' square: {}", from_str)))?;
    let to_sq = algebraic_to_index(to_str)
                .ok_or_else(|| MoveError::InvalidFormat(format!("Invalid 'to' square: {}", to_str)))?;

    let promotion = if trimmed.len() == 5 {
        match trimmed.chars().nth(4).map(|c| c.to_ascii_lowercase()) {
            Some('q') => Some(PieceType::Queen),
            Some('r') => Some(PieceType::Rook),
            Some('b') => Some(PieceType::Bishop),
            Some('n') => Some(PieceType::Knight),
            Some(other) => return Err(MoveError::InvalidPromotion(format!("Invalid promotion character: '{}'. Use q, r, b, or n.", other))),
            None => return Err(MoveError::InternalError("Logic error parsing promotion char")), // Should be unreachable
        }
    } else { None };

    // Create the move struct. is_capture and is_castle are set later during validation/application.
    // We don't know if it's a capture yet. Legality check will determine this.
    Ok(Move { from_sq, to_sq, promotion, is_capture: false, is_castle: false })
}

// --- Helper to format Duration ---
fn format_duration(duration: Duration) -> String {
    let total_seconds = duration.as_secs();
    let minutes = total_seconds / 60;
    let seconds = total_seconds % 60;
    // Calculate millis from total duration for better consistency
    let total_millis = duration.as_millis();
    let display_millis = total_millis % 1000;
    format!("{:02}:{:02}.{:03}", minutes, seconds, display_millis)
}

// --- Main Game Loop ---

fn main() -> Result<(), Box<dyn Error>> {
    println!("Starting a new game (Bitboard Version with Zobrist, Precomputation, Pins).");
    let mut game_state: Option<Game> = Some(Game::new());
    let mut game_result: Option<GameResult> = None; // Store the final outcome

    println!("==============================");
    println!("|   Rust Chess (Enhanced)    |");
    println!("==============================");
    print_help();

    // Use a loop label for easier breaking on game end or quit
    'game_loop: while let Some(game) = &mut game_state {

        // 1. Check for automatic game end conditions *before* prompting
        if game_result.is_none() { // Only check if game isn't already decided
            game_result = game.check_automatic_game_end();
        }

        // 2. Handle Game End if result is determined
        if let Some(result) = game_result {
            println!("------------------------------------------");
            println!("{}", game); // Print final board state
            match result {
                GameResult::Win(color, reason) => println!("\n=== GAME OVER: {:?} wins by {:?}. ===", color, reason),
                GameResult::Draw(reason) => println!("\n=== GAME OVER: Draw by {:?}. ===", reason),
            }
            println!("Saving final game stats to '{}'...", DEFAULT_STATS_FILENAME);
            if let Err(e) = game.save_stats_to_file(DEFAULT_STATS_FILENAME, game_result) {
                eprintln!("Error: Failed to save final stats: {}", e);
            } else {
                println!("Stats saved successfully.");
            }
            break 'game_loop; // Exit the main game loop
        }

        // --- If game is ongoing ---
        // 3. Print State and Prompt
        println!("------------------------------------------");
        println!("{}", game); // Print current board state, time, history, etc.

        print!("\n{:?}'s turn. Enter move (e.g. e2e4, O-O) or command: ", game.current_state.turn);
        io::stdout().flush()?; // Ensure prompt appears before waiting for input

        // 4. Read Input
        let mut input_line = String::new();
        match io::stdin().read_line(&mut input_line) {
            Ok(0) => { // EOF detected
                println!("\nEnd of input detected. Quitting game.");
                 if let Err(e) = game.save_stats_to_file(DEFAULT_STATS_FILENAME, None) {
                     eprintln!("Warning: Failed to save stats before quitting on EOF: {}", e);
                 }
                game_state = None; continue 'game_loop; // Exit loop
            }
            Ok(_) => { /* Input received */ }
            Err(e) => { // Handle other read errors
                 eprintln!("Error reading input: {}. Try again or use 'quit'/'exit'.", e);
                 continue 'game_loop; // Ask for input again
            }
        }

        let input_trimmed = input_line.trim();
        if input_trimmed.is_empty() { continue 'game_loop; } // Ignore empty lines

        // 5. Process Input
        match parse_user_input(input_trimmed) {
            // --- Handle Standard Algebraic Moves ---
            Ok(UserInput::Move(mut parsed_move)) => {
                // Check if this move *requires* a promotion but didn't provide one
                let needs_promotion_prompt = {
                    let state = &game.current_state;
                    if let Some(piece) = state.get_piece_at(parsed_move.from_sq) {
                        if piece.kind == PieceType::Pawn && parsed_move.promotion.is_none() {
                            let promotion_rank_mask = if piece.color == Color::White { RANK_8 } else { RANK_1 };
                            (1u64 << parsed_move.to_sq) & promotion_rank_mask != 0
                        } else { false }
                    } else { false } // No piece at source
                };

                if needs_promotion_prompt {
                    // Check if the move *to* that square is potentially legal *at all* before prompting
                     let is_target_potentially_legal = game.generate_legal_moves(&game.current_state)
                         .iter()
                         .any(|m| m.from_sq == parsed_move.from_sq && m.to_sq == parsed_move.to_sq);

                    if !is_target_potentially_legal {
                        println!("Error: Moving pawn to {} is not a legal destination.", index_to_algebraic(parsed_move.to_sq));
                        continue 'game_loop; // Don't prompt if basic move is illegal
                    }


                    // Prompt for promotion piece type
                    loop {
                        print!("Promote pawn to? (q=Queen, r=Rook, b=Bishop, n=Knight): ");
                        io::stdout().flush()?;
                        let mut promo_input = String::new();
                        match io::stdin().read_line(&mut promo_input) {
                            Ok(0) => { println!("\nEnd of input during promotion. Cancelling move attempt."); parsed_move.promotion = None; break; } // Break inner loop, move attempt will likely fail
                            Ok(_) => {
                                match promo_input.trim().to_lowercase().chars().next() {
                                    Some('q') => { parsed_move.promotion = Some(PieceType::Queen); break; }, // Break inner loop
                                    Some('r') => { parsed_move.promotion = Some(PieceType::Rook); break; },
                                    Some('b') => { parsed_move.promotion = Some(PieceType::Bishop); break; },
                                    Some('n') => { parsed_move.promotion = Some(PieceType::Knight); break; },
                                    Some(_) | None => { println!("Invalid choice. Please enter q, r, b, or n."); } // Continue inner loop
                                }
                            }
                            Err(e) => { println!("\nError reading promotion choice: {}. Cancelling move attempt.", e); parsed_move.promotion = None; break; } // Break inner loop
                        }
                    } // End promotion prompt loop

                     // If promotion wasn't selected (e.g., EOF), the make_legal_move below will likely fail.
                     // It needs the promotion type to find the correct legal move.
                     if parsed_move.promotion.is_none() {
                         println!("Promotion choice required but not provided. Move cancelled.");
                         continue 'game_loop;
                     }
                }

                // Attempt to make the (potentially promotion-completed) move
                match game.make_legal_move(&parsed_move) {
                    Ok(()) => { /* Move successful, loop continues */ }
                    Err(e) => { println!("Error making move: {}", e); } // Print error, loop continues
                }
            } // End UserInput::Move

            // --- Handle Castling Moves ---
            Ok(UserInput::CastleKingside) | Ok(UserInput::CastleQueenside) => {
                let (king_from_sq, king_to_sq, notation) = match parse_user_input(input_trimmed).unwrap() { // Safe unwrap as we matched these variants
                    UserInput::CastleKingside => {
                        let color = game.current_state.turn;
                        let from = if color == Color::White { WHITE_KING_START } else { BLACK_KING_START };
                        let to = if color == Color::White { WHITE_KING_KS_CASTLE_DEST } else { BLACK_KING_KS_CASTLE_DEST };
                        (from, to, "O-O")
                    }
                    UserInput::CastleQueenside => {
                        let color = game.current_state.turn;
                        let from = if color == Color::White { WHITE_KING_START } else { BLACK_KING_START };
                        let to = if color == Color::White { WHITE_KING_QS_CASTLE_DEST } else { BLACK_KING_QS_CASTLE_DEST };
                        (from, to, "O-O-O")
                    }
                    _ => unreachable!(), // Should not happen
                };
                // Use the special constructor which sets the is_castle flag correctly
                let castle_move = Move::new_castle(king_from_sq, king_to_sq);

                match game.make_legal_move(&castle_move) {
                    Ok(()) => { /* Castle successful */ }
                    Err(e) => { println!("Error making move ({}): {}", notation, e); }
                }
            } // End UserInput::Castle*

            // --- Handle Commands ---
            Ok(UserInput::Command(command)) => {
                match command {
                    Command::OfferDraw => {
                        match game.offer_draw() {
                            Ok(()) => println!("Draw offer noted. Please make your move to activate it."),
                            Err(e) => println!("Error: {}", e),
                        }
                        // Turn does NOT pass here. Loop will prompt the same player again.
                    }
                    Command::AcceptDraw => {
                         match game.accept_draw() {
                             Ok(result) => { game_result = Some(result); }, // Set result to end game loop
                             Err(e) => println!("Error: {}", e),
                         }
                    }
                    Command::DeclineDraw => {
                         match game.decline_draw() {
                            Ok(()) => println!("Draw offer declined. It's still your turn."),
                            Err(e) => println!("Error: {}", e),
                         }
                        // Turn does NOT pass here. Loop prompts same player again.
                    }
                    Command::Resign => {
                        game_result = Some(game.resign()); // Set result to end game loop
                    }
                    Command::History => {
                        println!("(Move history with annotations is shown above the board each turn)");
                    }
                    Command::ClaimDraw => {
                         match game.claim_draw() {
                            Ok(result) => { game_result = Some(result); }, // Set result to end game loop
                            Err(e) => println!("Error: {}", e),
                         }
                    }
                    Command::Help => print_help(),
                    Command::Quit => {
                         println!("Quit command received.");
                         println!("Attempting to save game stats before quitting...");
                         if let Err(e) = game.save_stats_to_file(DEFAULT_STATS_FILENAME, None) {
                             eprintln!("Warning: Failed to save stats before quitting: {}", e);
                         } else {
                             println!("Stats saved to {}.", DEFAULT_STATS_FILENAME);
                         }
                         println!("Exiting game.");
                         game_state = None; // Signal loop termination
                    }
                    Command::SaveStats(filename) => {
                        match game.save_stats_to_file(&filename, game_result) { // Save current result if any
                            Ok(()) => { println!("Game stats saved to '{}'.", filename); }
                            Err(e) => println!("Error saving game stats: {}", e),
                        }
                    }
                } // End match command
            } // End UserInput::Command

            // --- Handle Input Parsing Errors ---
            Err(e) => {
                println!("Input Error: {}", e); // Print command/parse error
            }
        } // End match parse_user_input

    } // End 'game_loop: while let Some(game)

    // --- Post-Game ---
    println!("\nGame session finished.");
    Ok(()) // Indicate successful exit of the main function

} // End main

/// Prints available commands.
fn print_help() {
    println!("\nAvailable Commands:");
    println!("  <move>         Enter move in algebraic notation (e.g., e2e4, a7a8q)");
    println!("                 Or use standard castling notation: O-O (kingside), O-O-O (queenside).");
    println!("                 Promotion (q, r, b, n) is optional; will prompt if needed.");
    println!("                 NOTE: Making a move activates any draw offer you noted this turn,");
    println!("                       and implicitly declines any active offer from the opponent.");
    println!("  history        Show move history (usually displayed automatically).");
    println!("  offer draw     Note a draw offer; you must still make a move to activate it.");
    println!("  accept draw    Accept opponent's *active* draw offer (ends game).");
    println!("  decline draw   Explicitly decline opponent's *active* draw offer (your turn continues).");
    println!("  claim draw     Claim draw by 50-move or 3-fold repetition if rules apply (ends game).");
    println!("  resign         Forfeit the game (ends game).");
    println!("  savestats [file] Save game statistics (default: {}).", DEFAULT_STATS_FILENAME);
    println!("  help           Show this help message.");
    println!("  quit / exit    Exit the game (attempts to save stats).");
    println!();
}