// Project: Chess Game in Rust
// Author: Deenanath Dayal
// Date: 2025-04-01
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

/// Initial time allocated to each player in seconds. (15 minutes)
const INITIAL_TIME_SECONDS: u64 = 15 * 60;
/// Default filename for saving game statistics if none is provided.
const DEFAULT_STATS_FILENAME: &str = "chess_stats.json";

// --- Bitboard Constants ---
// These constants represent bitmasks for specific files and ranks on the chessboard.
// They are used for move generation logic, especially for preventing pieces from wrapping around the board edges.

/// Bitmask representing all squares on File A.
const FILE_A: u64 = 0x0101010101010101;
/// Bitmask representing all squares on File B.
const FILE_B: u64 = FILE_A << 1;
/// Bitmask representing all squares on File G.
const FILE_G: u64 = FILE_A << 6;
/// Bitmask representing all squares on File H.
const FILE_H: u64 = FILE_A << 7;

/// Bitmask representing all squares on Rank 1.
const RANK_1: u64 = 0x00000000000000FF;
/// Bitmask representing all squares on Rank 2.
const RANK_2: u64 = RANK_1 << 8;
/// Bitmask representing all squares on Rank 3. Needed for En Passant Zobrist hashing and pawn move logic.
const RANK_3: u64 = RANK_1 << 16;
/// Bitmask representing all squares on Rank 4. Needed for En Passant logic.
const RANK_4: u64 = RANK_1 << 24;
/// Bitmask representing all squares on Rank 5. Needed for En Passant logic.
const RANK_5: u64 = RANK_1 << 32;
/// Bitmask representing all squares on Rank 6. Needed for En Passant Zobrist hashing and pawn move logic.
const RANK_6: u64 = RANK_1 << 40;
/// Bitmask representing all squares on Rank 7.
const RANK_7: u64 = RANK_1 << 48;
/// Bitmask representing all squares on Rank 8.
const RANK_8: u64 = RANK_1 << 56;

/// Bitmask representing all squares *not* on File A.
const NOT_FILE_A: u64 = !FILE_A;
/// Bitmask representing all squares *not* on File B.
const NOT_FILE_B: u64 = !FILE_B;
/// Bitmask representing all squares *not* on File G.
const NOT_FILE_G: u64 = !FILE_G;
/// Bitmask representing all squares *not* on File H.
const NOT_FILE_H: u64 = !FILE_H;

/// Bitmask representing all squares *not* on Rank 1.
const NOT_RANK_1: u64 = !RANK_1;
/// Bitmask representing all squares *not* on Rank 2.
const NOT_RANK_2: u64 = !RANK_2;
/// Bitmask representing all squares *not* on Rank 7.
const NOT_RANK_7: u64 = !RANK_7;
/// Bitmask representing all squares *not* on Rank 8.
const NOT_RANK_8: u64 = !RANK_8;

// --- Square indices for castling ---
// These constants represent the 0-63 index of specific squares involved in castling.

/// Square index (0-63) for White's starting King position (e1).
const WHITE_KING_START: u8 = 4;
/// Square index (0-63) for White's Kingside Rook starting position (h1).
const WHITE_KS_ROOK_START: u8 = 7;
/// Square index (0-63) for White's Queenside Rook starting position (a1).
const WHITE_QS_ROOK_START: u8 = 0;
/// Square index (0-63) for White's King destination after Kingside castle (g1).
const WHITE_KING_KS_CASTLE_DEST: u8 = 6;
/// Square index (0-63) for White's King destination after Queenside castle (c1).
const WHITE_KING_QS_CASTLE_DEST: u8 = 2;

/// Square index (0-63) for Black's starting King position (e8).
const BLACK_KING_START: u8 = 60;
/// Square index (0-63) for Black's Kingside Rook starting position (h8).
const BLACK_KS_ROOK_START: u8 = 63;
/// Square index (0-63) for Black's Queenside Rook starting position (a8).
const BLACK_QS_ROOK_START: u8 = 56;
/// Square index (0-63) for Black's King destination after Kingside castle (g8).
const BLACK_KING_KS_CASTLE_DEST: u8 = 62;
/// Square index (0-63) for Black's King destination after Queenside castle (c8).
const BLACK_KING_QS_CASTLE_DEST: u8 = 58;


/// Directions for sliding piece (Rook, Bishop, Queen) attack and pin generation.
/// Each tuple represents (rank_delta, file_delta, is_diagonal).
const DIRECTIONS: &[(i8, i8, bool)] = &[ // (dr, df, is_diagonal)
    ( 1,  0, false), ( -1,  0, false), ( 0,  1, false), ( 0, -1, false), // Orthogonal
    ( 1,  1, true),  ( 1, -1, true),  (-1,  1, true),  (-1, -1, true),  // Diagonal
];


// --- Enums and Basic Structs ---

/// Represents the two colors in a chess game.
#[derive(Debug, Serialize, Deserialize, Copy, Clone, PartialEq, Eq, Hash)]
enum Color { White, Black }

impl Color {
    /// Returns the opposing color.
    fn opponent(&self) -> Color {
        match self { Color::White => Color::Black, Color::Black => Color::White }
    }
    /// Returns a numerical index for the color (0 for White, 1 for Black).
    /// Useful for indexing arrays, particularly in Zobrist hashing.
    fn index(&self) -> usize { // Helper for Zobrist indexing
        match self { Color::White => 0, Color::Black => 1 }
    }
}

/// Represents the different types of chess pieces.
#[derive(Debug, Serialize, Deserialize, Copy, Clone, PartialEq, Eq, Hash)]
enum PieceType { Pawn, Knight, Bishop, Rook, Queen, King }

impl PieceType {
    /// Returns a numerical index for the piece type (Pawn=0, Knight=1, ..., King=5).
    /// Useful for indexing arrays, particularly in Zobrist hashing.
     fn index(&self) -> usize { // Helper for Zobrist indexing
        match self {
            PieceType::Pawn => 0, PieceType::Knight => 1, PieceType::Bishop => 2,
            PieceType::Rook => 3, PieceType::Queen => 4, PieceType::King => 5,
        }
    }
}

/// Represents a single chess piece with its type and color.
#[derive(Debug, Serialize, Deserialize, Copy, Clone, PartialEq, Eq, Hash)]
struct Piece {
    /// The type of the piece (e.g., Pawn, Knight).
    kind: PieceType,
    /// The color of the piece (White or Black).
    color: Color,
}

impl Piece {
    /// Creates a new `Piece` instance.
    fn new(kind: PieceType, color: Color) -> Self { Piece { kind, color } }

    /// Returns the approximate material value of the piece.
    /// King value is typically 0 as its loss ends the game.
    fn value(&self) -> u32 {
        match self.kind {
            PieceType::Pawn => 1, PieceType::Knight => 3, PieceType::Bishop => 3,
            PieceType::Rook => 5, PieceType::Queen => 9, PieceType::King => 0,
        }
    }

    /// Creates a `Piece` from its standard single-character representation (e.g., 'P', 'n').
    /// Case determines color (uppercase = White, lowercase = Black).
    /// Returns `None` if the character is not a valid piece representation.
    /// Potentially useful for FEN parsing or other input methods.
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

/// Implements the `Display` trait for `Piece`, allowing pieces to be printed using their standard symbols.
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

/// Converts a square index (0-63) to standard algebraic notation (e.g., 4 -> "e1", 60 -> "e8").
/// Returns "??" if the index is out of bounds.
fn index_to_algebraic(index: u8) -> String {
    if index >= 64 { return "??".to_string(); }
    let rank = index / 8; // 0-7
    let file = index % 8; // 0-7
    let file_char = (b'a' + file) as char; // 'a' through 'h'
    let rank_char = (b'1' + rank) as char; // '1' through '8'
    format!("{}{}", file_char, rank_char)
}

/// Converts standard algebraic notation (e.g., "e4") to a square index (0-63).
/// Returns `None` if the input string is not valid algebraic notation.
fn algebraic_to_index(s: &str) -> Option<u8> {
    if s.len() != 2 { return None; }
    let mut chars = s.chars();
    let file_char = chars.next()?; // Get the first character (file)
    let rank_char = chars.next()?; // Get the second character (rank)
    let file = match file_char { 'a'..='h' => Some(file_char as u8 - b'a'), _ => None }?; // Convert 'a'-'h' to 0-7
    let rank = match rank_char { '1'..='8' => Some(rank_char as u8 - b'1'), _ => None }?; // Convert '1'-'8' to 0-7
    Some(rank * 8 + file) // Calculate the final index
}

// --- Move Representation ---

/// Represents a chess move, including source, destination, and potential promotion.
/// Also includes flags for move ordering and special move types determined during generation.
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
struct Move {
    /// The starting square index (0-63).
    from_sq: u8,
    /// The destination square index (0-63).
    to_sq: u8,
    /// If the move is a pawn promotion, specifies the piece type promoted to (Queen, Rook, Bishop, Knight).
    promotion: Option<PieceType>,
    /// Flag indicating if this move captures an opponent's piece. Set during pseudo-legal generation.
    /// Used for simple move ordering and potentially the fifty-move rule counter.
    #[serde(skip)] // Don't serialize this internal helper field
    is_capture: bool,
    /// Flag indicating if this move represents castling. Set during move generation.
    #[serde(skip)] // Don't serialize this internal helper field
    is_castle: bool,
}

impl Move {
    /// Creates a new standard move (non-castling).
    /// `is_capture` should be set based on whether the `to_sq` is occupied by an opponent piece
    /// during pseudo-legal move generation.
    /// This constructor also performs a *basic* check to see if the move *pattern* matches castling
    /// (e.g., e1g1, e8c8) and sets the `is_castle` flag accordingly. Full legality is checked later.
    fn new(from_sq: u8, to_sq: u8, promotion: Option<PieceType>, is_capture: bool) -> Self {
        // Basic check for castling pattern based only on king start/end squares
        let is_castle = (from_sq == WHITE_KING_START && (to_sq == WHITE_KING_KS_CASTLE_DEST || to_sq == WHITE_KING_QS_CASTLE_DEST)) ||
                        (from_sq == BLACK_KING_START && (to_sq == BLACK_KING_KS_CASTLE_DEST || to_sq == BLACK_KING_QS_CASTLE_DEST));
        Move { from_sq, to_sq, promotion, is_capture, is_castle }
    }

    /// Creates a new move specifically identified as castling during king move generation.
    /// Ensures the `is_castle` flag is true and `is_capture` is false.
    fn new_castle(from_sq: u8, to_sq: u8) -> Self {
        Move { from_sq, to_sq, promotion: None, is_capture: false, is_castle: true }
    }

    /// Returns the standard algebraic notation for the move.
    /// Handles standard moves ("e2e4"), promotions ("a7a8q"), and castling ("O-O", "O-O-O").
    fn to_algebraic_string(&self) -> String {
        if self.is_castle {
            // Determine kingside/queenside based on destination square relative to start
            if self.to_sq == WHITE_KING_KS_CASTLE_DEST || self.to_sq == BLACK_KING_KS_CASTLE_DEST {
                "O-O".to_string() // Kingside castle
            } else {
                "O-O-O".to_string() // Queenside castle
            }
        } else {
            // Format as: from_square + to_square + optional_promotion_char
            format!("{}{}{}",
                index_to_algebraic(self.from_sq),
                index_to_algebraic(self.to_sq),
                self.promotion.map_or(String::new(), |p| match p {
                    PieceType::Queen => "q", PieceType::Rook => "r",
                    PieceType::Bishop => "b", PieceType::Knight => "n",
                    // Invalid promotion types (King/Pawn) should be prevented earlier.
                    _ => "",
                }.to_string())
            )
        }
    }
}


// --- Precomputed Move Tables ---

// `lazy_static!` ensures these potentially expensive computations are done only once
// at program startup and the results are available globally and immutably.
lazy_static! {
    /// Precomputed knight attack bitboards. `KNIGHT_ATTACKS[sq]` gives a bitboard of all squares
    /// attacked by a knight on `sq`.
    static ref KNIGHT_ATTACKS: [u64; 64] = compute_knight_attacks();
    /// Precomputed king attack bitboards. `KING_ATTACKS[sq]` gives a bitboard of all squares
    /// attacked by a king on `sq`.
    static ref KING_ATTACKS: [u64; 64] = compute_king_attacks();
    // static ref PAWN_ATTACKS: [[u64; 64]; 2] = compute_pawn_attacks(); // Could add if needed for performance
    /// Globally accessible instance of the Zobrist hashing table containing precomputed random keys.
    static ref ZOBRIST: ZobristTable = ZobristTable::new();
}

/// Computes the attack bitboards for knights on every square of the board.
/// Handles board edge wrapping correctly using `NOT_FILE` and `NOT_RANK` masks.
/// Returns an array where the index corresponds to the knight's square (0-63).
fn compute_knight_attacks() -> [u64; 64] {
    let mut attacks = [0u64; 64];
    for sq in 0..64 {
        let from_bb = 1u64 << sq;
        let mut moves: u64 = 0;
        // Knight L-shape move offsets: +17, +15, +10, +6, -17, -15, -10, -6
        // Apply masks *before* shifting to prevent wrapping around edges.
        // e.g., a knight on h1 cannot move "up 2, right 1" off the board.
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

/// Computes the attack bitboards for kings on every square of the board.
/// Handles board edge wrapping correctly using `NOT_FILE` and `NOT_RANK` masks.
/// Returns an array where the index corresponds to the king's square (0-63).
fn compute_king_attacks() -> [u64; 64] {
    let mut attacks = [0u64; 64];
    for sq in 0..64 {
        let from_bb = 1u64 << sq;
        let mut moves: u64 = 0;
        // King moves one square in any direction. Offsets: +7, +8, +9, -1, +1, -9, -8, -7
        // Apply masks *before* shifting to prevent wrapping around edges.
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

/// Stores precomputed random 64-bit keys for Zobrist hashing of chess positions.
/// Allows for efficient incremental updates of the hash key when moves are made.
#[derive(Debug, Clone)]
struct ZobristTable {
    /// `piece_keys[color_idx][piece_type_idx][square_idx]` gives the key for a piece at a square.
    piece_keys: [[[u64; 64]; 6]; 2], // [Color][PieceType][Square]
    /// `castling_keys[wk][wq][bk][bq]` gives the key for a specific combination of castling rights.
    /// Indices are 0 (false) or 1 (true).
    castling_keys: [[[[u64; 2]; 2]; 2]; 2], // [WK][WQ][BK][BQ]
    /// `en_passant_keys[square_idx]` gives the key to XOR if `square_idx` is the en passant target square.
    /// Keys are only generated for valid target squares (rank 3 and 6), others remain 0.
    en_passant_keys: [u64; 64], // Index corresponds to target EP square (a3..h3, a6..h6)
    /// Key to XOR into the hash if it's Black's turn to move.
    black_to_move_key: u64,
}

impl ZobristTable {
    /// Creates a new `ZobristTable` and initializes it with pseudo-random 64-bit keys.
    /// Uses a fixed seed for the random number generator (`StdRng`) to ensure that
    /// the generated keys are consistent across program runs, which is important for
    /// reproducibility and debugging, and potentially for transposition tables if implemented.
    fn new() -> Self {
        // Use a fixed seed for deterministic key generation
        let mut rng = StdRng::seed_from_u64(0xDEADBEEFCAFEBABE); // Consistent seed
        let mut table = ZobristTable {
            piece_keys: [[([0; 64]); 6]; 2], // Initialize with zeros
            castling_keys: [[[[0; 2]; 2]; 2]; 2], // Initialize with zeros
            en_passant_keys: [0; 64], // Initialize with zeros
            black_to_move_key: rng.next_u64(), // Generate side-to-move key
        };

        // Generate keys for each piece type, color, and square
        for color in 0..2 { // 0: White, 1: Black
            for piece_type in 0..6 { // 0: Pawn, ..., 5: King
                for square in 0..64 {
                    table.piece_keys[color][piece_type][square] = rng.next_u64();
                }
            }
        }

        // Generate keys for all 16 possible castling right combinations
        for wk in 0..2 { // White Kingside (0: false, 1: true)
            for wq in 0..2 { // White Queenside
                for bk in 0..2 { // Black Kingside
                    for bq in 0..2 { // Black Queenside
                        table.castling_keys[wk][wq][bk][bq] = rng.next_u64();
                    }
                }
            }
        }

        // Generate keys only for valid en passant target squares (rank 3 and rank 6)
        for file in 0..8 {
             // Rank 3 target square index (e.g., a3, b3, ...)
             let sq_rank3 = (RANK_3.trailing_zeros() + file) as usize;
             if sq_rank3 < 64 { table.en_passant_keys[sq_rank3] = rng.next_u64(); }
             // Rank 6 target square index (e.g., a6, b6, ...)
             let sq_rank6 = (RANK_6.trailing_zeros() + file) as usize;
             if sq_rank6 < 64 { table.en_passant_keys[sq_rank6] = rng.next_u64(); }
        }
        // Squares not on rank 3 or 6 will keep their 0 key, so XORing them has no effect.

        table
    }

    /// Retrieves the Zobrist key component for a specific piece at a given square.
    /// Assumes `sq` is a valid index (0-63).
    #[inline(always)]
    fn piece(&self, piece: Piece, sq: u8) -> u64 {
        // Assumes sq is in 0..64 range, relies on caller for valid input.
        self.piece_keys[piece.color.index()][piece.kind.index()][sq as usize]
    }

    /// Retrieves the Zobrist key component corresponding to the current castling rights.
    #[inline(always)]
    fn castling(&self, rights: CastlingRights) -> u64 {
        self.castling_keys[rights.white_kingside as usize][rights.white_queenside as usize]
                          [rights.black_kingside as usize][rights.black_queenside as usize]
    }

    /// Retrieves the Zobrist key component for the en passant target square.
    /// Returns 0 if `ep_square` is `None` or the square index is invalid (>= 64),
    /// or if the square is not a valid EP target rank (implicitly, as those keys are 0).
    #[inline(always)]
    fn en_passant(&self, ep_square: Option<u8>) -> u64 {
        match ep_square {
            // Access the key only if sq is within the valid range 0-63.
            Some(sq) if sq < 64 => self.en_passant_keys[sq as usize],
            _ => 0, // Return 0 if no EP square, invalid index, or not a valid EP rank.
        }
    }

    /// Retrieves the Zobrist key component representing the side to move.
    /// Returns the specific `black_to_move_key` if `color` is Black, otherwise returns 0.
    /// XORing with 0 has no effect, so this correctly handles White's turn.
    #[inline(always)]
    fn side_to_move(&self, color: Color) -> u64 {
        if color == Color::Black { self.black_to_move_key } else { 0 }
    }
}

// --- Bitboard State ---

/// Represents the castling rights for both players.
#[derive(Debug, Serialize, Deserialize, Copy, Clone, PartialEq, Eq, Hash)]
struct CastlingRights {
    /// Can White castle kingside?
    white_kingside: bool,
    /// Can White castle queenside?
    white_queenside: bool,
    /// Can Black castle kingside?
    black_kingside: bool,
    /// Can Black castle queenside?
    black_queenside: bool,
}

impl CastlingRights {
    /// Returns the initial castling rights at the start of a standard game.
    fn initial() -> Self { Self { white_kingside: true, white_queenside: true, black_kingside: true, black_queenside: true } }

    /// Updates the castling rights when a king of the specified color moves.
    /// Both kingside and queenside rights are revoked for that color.
    fn king_moved(&mut self, color: Color) {
        if color == Color::White {
            self.white_kingside = false;
            self.white_queenside = false;
        } else {
            self.black_kingside = false;
            self.black_queenside = false;
        }
    }

    // Note: Logic for rook moves/captures affecting castling rights is handled directly
    // within the move application functions (`apply_legal_move`, `apply_move_immutable_no_zobrist`)
    // by checking the 'from' or 'to' square of the move.
}


/// Represents the complete state of the chessboard using bitboards.
/// Includes piece positions, turn, castling rights, en passant target, and move clocks.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct BitboardState {
    // Piece bitboards: Each u64 has a bit set for each square occupied by that piece type/color.
    wp: u64, wn: u64, wb: u64, wr: u64, wq: u64, wk: u64, // White pieces
    bp: u64, bn: u64, bb: u64, br: u64, bq: u64, bk: u64, // Black pieces

    // Occupancy bitboards: Aggregate boards for faster checks.
    /// Bitboard of all squares occupied by any white piece.
    white_occupied: u64,
    /// Bitboard of all squares occupied by any black piece.
    black_occupied: u64,
    /// Bitboard of all squares occupied by any piece (White or Black).
    occupied: u64,

    // Game state variables
    /// The color of the player whose turn it is to move.
    turn: Color,
    /// Current castling rights for both players.
    castling_rights: CastlingRights,
    /// The target square index (0-63) for a potential en passant capture, if one exists.
    /// `None` if no en passant capture is possible on the next move.
    en_passant_square: Option<u8>,
    /// Counts halfmoves since the last capture or pawn advance. Used for the fifty-move rule.
    halfmove_clock: u32,
    /// Starts at 1 and increments after Black moves. Used to track the total number of full moves.
    fullmove_number: u32,
}

impl BitboardState {
    /// Creates the standard initial chessboard state.
    fn initial() -> Self {
        // White piece starting positions
        let wp = RANK_2; // Pawns on rank 2
        let wn = (1 << 1) | (1 << 6); // Knights on b1, g1
        let wb = (1 << 2) | (1 << 5); // Bishops on c1, f1
        let wr = (1 << WHITE_QS_ROOK_START) | (1 << WHITE_KS_ROOK_START); // Rooks on a1, h1
        let wq = 1 << 3; // Queen on d1
        let wk = 1 << WHITE_KING_START; // King on e1

        // Black piece starting positions (shifted up 7 ranks)
        let bp = RANK_7; // Pawns on rank 7
        let bn = ((1 << 1) | (1 << 6)) << 56; // Knights on b8, g8
        let bb = ((1 << 2) | (1 << 5)) << 56; // Bishops on c8, f8
        let br = (1 << BLACK_QS_ROOK_START) | (1 << BLACK_KS_ROOK_START); // Rooks on a8, h8
        let bq = (1 << 3) << 56; // Queen on d8
        let bk = 1 << BLACK_KING_START; // King on e8

        // Calculate initial occupancy boards
        let white_occupied = wp | wn | wb | wr | wq | wk;
        let black_occupied = bp | bn | bb | br | bq | bk;
        let occupied = white_occupied | black_occupied;

        BitboardState {
            wp, wn, wb, wr, wq, wk,
            bp, bn, bb, br, bq, bk,
            white_occupied, black_occupied, occupied,
            turn: Color::White, // White moves first
            castling_rights: CastlingRights::initial(),
            en_passant_square: None, // No EP target initially
            halfmove_clock: 0, // Starts at 0
            fullmove_number: 1, // Starts at 1
        }
    }

    /// Recalculates the aggregate occupancy bitboards (`white_occupied`, `black_occupied`, `occupied`)
    /// based on the current state of the individual piece bitboards.
    /// This MUST be called after any direct manipulation of the piece bitboards (e.g., in move application).
    #[inline(always)]
    fn update_occupancy(&mut self) {
        self.white_occupied = self.wp | self.wn | self.wb | self.wr | self.wq | self.wk;
        self.black_occupied = self.bp | self.bn | self.bb | self.br | self.bq | self.bk;
        self.occupied = self.white_occupied | self.black_occupied;
    }

     /// Returns an immutable reference to the bitboard for a specific piece type and color.
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
    /// Allows direct modification of the piece bitboard (use with caution, requires `update_occupancy`).
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

    /// Sets the bit corresponding to `sq` on the appropriate piece bitboard.
    /// Also XORs the corresponding Zobrist key for the piece/square into the provided `zobrist_key`.
    /// Assumes the square was previously empty of this specific piece type/color.
    /// # Parameters
    /// * `sq`: The square index (0-63) to set the piece on.
    /// * `piece_type`: The type of the piece being placed.
    /// * `color`: The color of the piece being placed.
    /// * `zobrist_key`: A mutable reference to the game's current Zobrist key to be updated.
    fn set_piece_at(&mut self, sq: u8, piece_type: PieceType, color: Color, zobrist_key: &mut u64) {
        let bb = self.get_piece_board_mut(piece_type, color);
        let mask = 1u64 << sq;
        // Check if the bit is not already set to avoid XORing the key twice if called incorrectly.
        if *bb & mask == 0 {
            *bb |= mask; // Set the bit on the piece board
            // XOR the piece's Zobrist key into the main hash
            *zobrist_key ^= ZOBRIST.piece(Piece::new(piece_type, color), sq);
        }
    }

    /// Clears the bit corresponding to `sq` from *all* piece bitboards.
    /// If a piece was present on `sq`, its Zobrist key is XORed out of the provided `zobrist_key`.
    /// # Parameters
    /// * `sq`: The square index (0-63) to clear.
    /// * `zobrist_key`: A mutable reference to the game's current Zobrist key to be updated.
    /// # Returns
    /// * `Some(Piece)` containing the piece that was removed from the square, if any.
    /// * `None` if the square was already empty.
    fn clear_square(&mut self, sq: u8, zobrist_key: &mut u64) -> Option<Piece> {
        let mask = 1u64 << sq;
        let inv_mask = !mask; // Mask to clear the bit
        let mut captured: Option<Piece> = None;

        // Check each piece bitboard. If the bit is set, clear it and record the piece type/color.
        // Using `else if` ensures only one piece type is found per square.
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

        // If a piece was found and removed, XOR its key out of the main hash.
        if let Some(piece) = captured {
            *zobrist_key ^= ZOBRIST.piece(piece, sq);
        }

        captured // Return the piece that was removed (or None)
    }


    /// Gets the piece (type and color) at a specific square index (0-63).
    /// Checks occupancy bitboards first for a potentially faster exit if the square is empty.
    /// # Parameters
    /// * `sq`: The square index (0-63) to query.
    /// # Returns
    /// * `Some(Piece)` if a piece is present on the square.
    /// * `None` if the square is empty.
    #[inline(always)]
    fn get_piece_at(&self, sq: u8) -> Option<Piece> {
        let mask = 1u64 << sq;
        // Quick check: if the square isn't in the combined occupied bitboard, it must be empty.
        if self.occupied & mask == 0 { return None; }

        // If occupied, check which color's occupancy board it's in.
        if self.white_occupied & mask != 0 {
            // Check white piece boards
            if self.wp & mask != 0 { Some(Piece::new(PieceType::Pawn, Color::White)) }
            else if self.wn & mask != 0 { Some(Piece::new(PieceType::Knight, Color::White)) }
            else if self.wb & mask != 0 { Some(Piece::new(PieceType::Bishop, Color::White)) }
            else if self.wr & mask != 0 { Some(Piece::new(PieceType::Rook, Color::White)) }
            else if self.wq & mask != 0 { Some(Piece::new(PieceType::Queen, Color::White)) }
            else if self.wk & mask != 0 { Some(Piece::new(PieceType::King, Color::White)) }
            // Should be unreachable if occupancy maps are correct, but return None as fallback.
            else { None }
        } else { // Must be black occupied (since combined 'occupied' was set)
            // Check black piece boards
            if self.bp & mask != 0 { Some(Piece::new(PieceType::Pawn, Color::Black)) }
            else if self.bn & mask != 0 { Some(Piece::new(PieceType::Knight, Color::Black)) }
            else if self.bb & mask != 0 { Some(Piece::new(PieceType::Bishop, Color::Black)) }
            else if self.br & mask != 0 { Some(Piece::new(PieceType::Rook, Color::Black)) }
            else if self.bq & mask != 0 { Some(Piece::new(PieceType::Queen, Color::Black)) }
            else if self.bk & mask != 0 { Some(Piece::new(PieceType::King, Color::Black)) }
            // Should be unreachable if occupancy maps are correct.
            else { None }
        }
    }

    /// Finds the square index (0-63) of the king for a given color.
    /// Uses `trailing_zeros()` on the king's bitboard, which is efficient as there's only one king.
    /// # Returns
    /// * `Some(u8)` containing the king's square index if found.
    /// * `None` if the king bitboard for that color is empty (which indicates an invalid/corrupt state).
    #[inline(always)]
    fn find_king(&self, color: Color) -> Option<u8> {
        let king_board = if color == Color::White { self.wk } else { self.bk };
        if king_board == 0 {
            None // King is missing!
        } else {
            // `trailing_zeros()` counts the number of zero bits from the least significant bit
            // until the first set bit, which gives the index of that bit (the king's square).
            Some(king_board.trailing_zeros() as u8)
        }
    }

    /// Returns the occupancy bitboard for the specified color (`white_occupied` or `black_occupied`).
    #[inline(always)]
    fn occupied_by_color(&self, color: Color) -> u64 {
        if color == Color::White { self.white_occupied } else { self.black_occupied }
    }

    /// Calculates the Zobrist hash key for the current board state from scratch.
    /// Iterates through all pieces on the board and XORs their corresponding keys,
    /// then XORs the keys for castling rights, en passant square, and side to move.
    /// Useful for initializing the hash key or for verification purposes. Slower than
    /// incremental updates during move application.
    /// # Returns
    /// The calculated 64-bit Zobrist hash key for the state.
    fn calculate_zobrist_key(&self) -> u64 {
        let mut key = 0u64;
        let zob = &*ZOBRIST; // Dereference lazy_static once for efficiency

        // Iterate through both colors
        for color_idx in 0..2 {
            let color = if color_idx == 0 { Color::White } else { Color::Black };
            // Iterate through all piece types
            for piece_idx in 0..6 {
                let piece_type = match piece_idx {
                    0 => PieceType::Pawn, 1 => PieceType::Knight, 2 => PieceType::Bishop,
                    3 => PieceType::Rook, 4 => PieceType::Queen, _ => PieceType::King,
                };
                let piece = Piece::new(piece_type, color);
                let mut board = self.get_piece_board(piece_type, color);
                // Iterate through each set bit (piece) on the current piece board
                while board != 0 {
                    let sq = board.trailing_zeros() as u8; // Find the index of the piece
                    key ^= zob.piece(piece, sq); // XOR the piece's key into the hash
                    board &= board - 1; // Clear the least significant bit (removes the processed piece)
                }
            }
        }

        // XOR in the keys for other state components
        key ^= zob.castling(self.castling_rights); // Castling rights
        key ^= zob.en_passant(self.en_passant_square); // En passant target square (if any)
        key ^= zob.side_to_move(self.turn); // Side to move

        key
    }
}

// --- Event History and Stats Saving ---

/// Records details about a single move made during the game.
#[derive(Debug, Clone, Serialize)]
struct MoveRecord {
    /// The algebraic notation of the move as it was played (e.g., "e2e4", "O-O", "a7a8q").
    mv_algebraic: String,
    /// The time taken by the player to make this move.
    time_taken: Duration,
    /// The color of the player who made the move.
    player: Color,
    /// Was the opponent put in check by this move?
    is_check: bool,
    /// Was the opponent checkmated by this move?
    is_checkmate: bool,
}

/// Enumerates the reasons why a game might end in a draw.
#[derive(Debug, Serialize, Deserialize, Clone, Copy, PartialEq, Eq)]
enum DrawReason {
    /// Draw automatically declared due to the 75-move rule (FIDE 9.6.2).
    SeventyFiveMoveRule,
    /// Draw automatically declared due to the same position occurring 5 times (FIDE 9.6.1).
    FivefoldRepetition,
    /// Draw automatically declared because checkmate is impossible (e.g., K vs K, K+N vs K) (FIDE 5.2.2).
    InsufficientMaterial,
    /// Draw due to timeout when the timed-out player's opponent has insufficient material to mate (FIDE 6.9).
    TimeoutVsInsufficientMaterial,
    /// Draw because the player whose turn it is has no legal moves but is not in check (FIDE 5.2.1).
    Stalemate,
    /// Draw agreed upon by both players.
    Agreement,
    /// Draw claimed by a player under the 50-move rule (clock >= 100) (FIDE 9.3).
    FiftyMoveRuleClaimed,
    /// Draw claimed by a player because the current position has appeared 3 times (FIDE 9.2).
    ThreefoldRepetitionClaimed,
}

/// Represents significant events that occur during a game, beyond just moves.
#[derive(Debug, Clone, Serialize)]
enum GameEvent {
    /// A standard move was made.
    Move(MoveRecord),
    /// A player offered a draw.
    OfferDraw(Color),
    /// A player accepted a draw offer.
    AcceptDraw(Color),
    /// A player declined a draw offer.
    DeclineDraw(Color),
    /// A player resigned.
    Resign(Color),
    /// A player claimed a draw based on a specific rule.
    ClaimDraw(Color, DrawReason),
}

/// A summarized version of non-move game events, suitable for inclusion in final game statistics.
#[derive(Debug, Serialize)]
#[serde(tag = "type", content = "details")] // Use tagged enum serialization for clarity in JSON
enum GameEventSummary {
    /// A player offered a draw.
    OfferDraw { player: Color },
    /// A player accepted a draw offer.
    AcceptDraw { player: Color },
    /// A player declined a draw offer.
    DeclineDraw { player: Color },
    /// A player resigned.
    Resign { player: Color },
    /// A player claimed a draw.
    ClaimDraw { player: Color, reason: DrawReason },
}

/// Represents the definitive reason for the game's conclusion, used in final statistics.
/// This combines win/draw reasons into a single enum for serialization.
#[derive(Debug, Serialize, Clone, Copy, PartialEq, Eq)]
enum GameResultReason {
    /// Game ended in checkmate.
    Checkmate { winner: Color, loser: Color },
    /// Game ended due to timeout.
    Timeout { winner: Color, loser: Color },
    /// Game ended due to resignation.
    Resignation { winner: Color, loser: Color },
    /// Game ended in stalemate.
    Stalemate,
    /// Game ended by 75-move rule.
    SeventyFiveMoveRule,
    /// Game ended by fivefold repetition.
    FivefoldRepetition,
    /// Game ended by insufficient material.
    InsufficientMaterial,
    /// Game ended by timeout vs insufficient material.
    TimeoutVsInsufficientMaterial,
    /// Game ended by agreement.
    Agreement,
    /// Game ended by claimed 50-move rule draw.
    FiftyMoveRuleClaimed,
    /// Game ended by claimed threefold repetition draw.
    ThreefoldRepetitionClaimed,
}

/// Contains comprehensive statistics for a completed game, suitable for serialization (e.g., to JSON).
#[derive(Debug, Serialize)]
struct GameStats {
    /// The final result of the game (win/draw and reason). `None` if the game was terminated prematurely without result.
    result: Option<GameResultReason>,
    /// Time remaining for White at the end of the game.
    white_final_time_remaining: Duration,
    /// Time remaining for Black at the end of the game.
    black_final_time_remaining: Duration,
    /// Approximate total duration of the game calculated from move times (in seconds).
    total_game_duration_secs: u64,
    /// List of moves made by White, with timing and annotations.
    white_moves: Vec<MoveStat>,
    /// List of moves made by Black, with timing and annotations.
    black_moves: Vec<MoveStat>,
    /// Summary of significant non-move events that occurred.
    game_events: Vec<GameEventSummary>,
}

/// Statistics for a single move, used within `GameStats`.
#[derive(Debug, Serialize)]
struct MoveStat {
    /// The algebraic notation of the move (e.g., "e4", "O-O", "Nf3+").
    move_algebraic: String,
    /// Time taken for this specific move.
    time_taken: Duration,
    /// Annotation indicating check (+) or checkmate (#). Empty string otherwise.
    annotation: String,
}

// --- Pinned Piece Information ---

/// Stores information about pinned pieces for the player whose turn it is.
/// Calculated at the beginning of legal move generation.
#[derive(Debug, Clone)]
struct PinInfo {
    /// A bitboard where each set bit corresponds to a square (0-63) occupied by one
    /// of the current player's pieces that is absolutely pinned to their king.
    pinned_pieces: u64,
    /// An array mapping each square index (0-63) to a bitboard.
    /// If a piece on `sq` is pinned (`pinned_pieces & (1 << sq) != 0`), then
    /// `pin_restriction_map[sq]` contains the bitboard of all squares the pinned piece
    /// can legally move to (i.e., squares along the pin ray towards or away from the king,
    /// including capturing the pinning piece).
    /// If a square `sq` does not contain a pinned piece, `pin_restriction_map[sq]` is 0.
    pin_restriction_map: [u64; 64],
}

/// Manual implementation of `Default` for `PinInfo`.
/// Initializes with no pinned pieces and an empty restriction map.
impl Default for PinInfo {
    fn default() -> Self {
        PinInfo {
            pinned_pieces: 0,
            // Initialize the array with 64 zeros.
            pin_restriction_map: [0u64; 64],
        }
    }
}


// --- Game State ---

/// Represents the entire state of a running chess game.
/// Includes the board state, history, timers, captured pieces, and draw offer status.
#[derive(Debug, Clone, Serialize)]
struct Game {
    /// The current state of the board using bitboards and associated state variables.
    current_state: BitboardState,
    /// The Zobrist hash key corresponding to the `current_state`. Updated incrementally.
    #[serde(skip)] // Don't serialize the hash key itself, it's derived from the state.
    zobrist_key: u64,
    /// A history tracking the number of times each Zobrist hash key (position) has occurred.
    /// Used for detecting threefold and fivefold repetition.
    #[serde(skip)] // Don't serialize the history map directly; it can be large and is stateful.
    zobrist_history: HashMap<u64, u8>,
    /// A chronological log of all significant game events (moves, offers, resignations, etc.).
    event_history: Vec<GameEvent>,
    /// List of Black pieces captured by White.
    captured_white: Vec<Piece>,
    /// List of White pieces captured by Black.
    captured_black: Vec<Piece>,
    /// If `Some(color)`, indicates that `color` (the opponent) made a draw offer on their *last* turn,
    /// and it is currently active, awaiting response from the current player.
    /// Cleared when the current player moves, accepts, or declines.
    draw_offer: Option<Color>,
    /// If `Some(color)`, indicates that `color` (the current player) has *signaled* an intent
    /// to offer a draw (`offer draw` command) but has not yet made their move.
    /// This offer becomes active (moves to `draw_offer`) immediately after they make their move.
    /// Cleared when the current player makes a move.
    #[serde(skip)] // Transient state, not needed for serialization.
    pending_draw_offer: Option<Color>,
    /// Time remaining for the White player.
    white_time_remaining: Duration,
    /// Time remaining for the Black player.
    black_time_remaining: Duration,
    /// Records the `Instant` when the current player's turn began. Used to calculate time spent on the move.
    /// `None` if the game hasn't started or potentially between turns.
    #[serde(skip)] // Runtime state, not for serialization.
    turn_start_time: Option<Instant>,
}

/// Implements the `Display` trait for `Game`, providing a user-friendly text representation
/// of the current game state, including the board, captured pieces, time, turn info,
/// move history, and draw offer status.
impl fmt::Display for Game {
     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let state = &self.current_state;

        // --- Captured Pieces ---
        // Display captured pieces sorted by value for consistency.
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
        // Print the board from rank 8 down to rank 1.
        writeln!(f, "  +-----------------+")?;
        for rank_idx in (0..8).rev() { // Iterate ranks 7 down to 0
            write!(f, "{} | ", rank_idx + 1)?; // Print rank number (1-8)
            for file_idx in 0..8 { // Iterate files 0 to 7 (a to h)
                let sq_index = (rank_idx * 8 + file_idx) as u8;
                match state.get_piece_at(sq_index) {
                    Some(piece) => write!(f, "{} ", piece)?, // Print piece symbol
                    None => write!(f, ". ")?, // Print '.' for empty square
                }
            }
            writeln!(f, "|")?; // End of rank
        }
        writeln!(f, "  +-----------------+")?;
        writeln!(f, "    a b c d e f g h")?; // Print file letters

        // --- Game State Info ---
        writeln!(f, "Turn: {:?}", state.turn)?;
        // Display castling rights using standard FEN notation (K=WK, Q=WQ, k=BK, q=BQ).
        writeln!(f, "Castling: W:{}{}, B:{}{}",
            if state.castling_rights.white_kingside { "K" } else { "-" },
            if state.castling_rights.white_queenside { "Q" } else { "-" },
            if state.castling_rights.black_kingside { "k" } else { "-" },
            if state.castling_rights.black_queenside { "q" } else { "-" }
        )?;
        // Display en passant target square in algebraic notation, or "-" if none.
        if let Some(ep_sq) = state.en_passant_square { writeln!(f, "En Passant Target: {}", index_to_algebraic(ep_sq))?; }
        else { writeln!(f, "En Passant Target: -")?; }
        writeln!(f, "Halfmove Clock: {}", state.halfmove_clock)?;
        writeln!(f, "Fullmove Number: {}", state.fullmove_number)?;
        // Optional: Display Zobrist key for debugging.
        // writeln!(f, "Zobrist Key: {:016x}", self.zobrist_key)?;

        // --- Annotated Move History Display ---
        // Formats the move history like "1. e4 e5 2. Nf3 Nc6+"
        let mut move_num = 1; // Start with move number 1
        let mut white_move_record: Option<&MoveRecord> = None; // Temporarily store White's move to pair with Black's
        let has_moves = self.event_history.iter().any(|ev| matches!(ev, GameEvent::Move(_)));

        if has_moves {
            writeln!(f, "Move History:")?;
            for event in &self.event_history {
                if let GameEvent::Move(record) = event {
                    if record.player == Color::White {
                         // If there was a pending white move from a previous iteration (e.g., game ended after black's last move), print it now.
                         if let Some(wm) = white_move_record.take() {
                              let annotation = if wm.is_checkmate { "#" } else if wm.is_check { "+" } else { "" };
                              // Print White's move alone, increment move number.
                              writeln!(f, "{}. {}{}", move_num, wm.mv_algebraic, annotation)?;
                              move_num += 1;
                         }
                         // Store the current white move to wait for black's move or print at the end.
                         white_move_record = Some(record);
                    } else { // Black's move
                        if let Some(wm) = white_move_record.take() { // If we have a preceding White move to pair with
                            let white_annotation = if wm.is_checkmate { "#" } else if wm.is_check { "+" } else { "" };
                            // Print "MoveNum. WhiteMove Annotation" (no newline yet)
                            write!(f, "{}. {}{}", move_num, wm.mv_algebraic, white_annotation)?;

                            let black_annotation = if record.is_checkmate { "#" } else if record.is_check { "+" } else { "" };
                            // Print " BlackMove Annotation" (with newline)
                            writeln!(f, " {}{}", record.mv_algebraic, black_annotation)?;
                            move_num += 1; // Increment move number after the pair is complete.
                        } else {
                            // Black moved first, or White's move record was missing. Print Black's move with ellipsis.
                            let black_annotation = if record.is_checkmate { "#" } else if record.is_check { "+" } else { "" };
                            // Use the current move number.
                            writeln!(f, "{}. ... {}{}", move_num, record.mv_algebraic, black_annotation)?;
                            move_num += 1; // Increment move number even if only Black's move is printed.
                        }
                    }
                }
            }
             // If the game ended after White's last move, print the stored white move record now.
             if let Some(wm) = white_move_record {
                 let annotation = if wm.is_checkmate { "#" } else if wm.is_check { "+" } else { "" };
                 // Use the current (final) move number.
                 writeln!(f, "{}. {}{}", move_num, wm.mv_algebraic, annotation)?;
            }
        }

        // --- Repetition Count (Using Zobrist History) ---
        // Display how many times the current position has occurred.
        let rep_count = self.zobrist_history.get(&self.zobrist_key).unwrap_or(&0);
        if *rep_count > 1 { writeln!(f, "Position Repetitions: {}", rep_count)?; }

        // --- Draw Offer Display ---
        // Display active draw offer from the opponent.
        if let Some(offering_color) = self.draw_offer {
             if offering_color == state.turn.opponent() {
                 writeln!(f, "--- {:?} has offered a draw! ('accept draw' / 'decline draw' / move) ---", offering_color)?;
             }
        }
        // Display if the current player has noted a pending draw offer.
        else if self.pending_draw_offer == Some(state.turn) {
             writeln!(f, "--- (Draw offer noted, will be active after your move) ---")?;
        }

        Ok(())
    }
}


// --- Game Implementation ---

impl Game {
    /// Creates a new `Game` instance, initializing the board state, timers,
    /// Zobrist key and history, and other game parameters to their starting values.
    fn new() -> Self {
        let initial_time = Duration::from_secs(INITIAL_TIME_SECONDS);
        let initial_state = BitboardState::initial(); // Get the starting board state
        let initial_zobrist_key = initial_state.calculate_zobrist_key(); // Calculate the initial hash
        let mut zobrist_history = HashMap::new();
        // Record the initial position as occurring once
        zobrist_history.insert(initial_zobrist_key, 1);

        Game {
            current_state: initial_state,
            zobrist_key: initial_zobrist_key,
            zobrist_history,
            white_time_remaining: initial_time,
            black_time_remaining: initial_time,
            turn_start_time: Some(Instant::now()), // Start the timer for White's first turn
            event_history: Vec::new(), // Start with empty history
            captured_white: Vec::new(), // No captures initially
            captured_black: Vec::new(), // No captures initially
            draw_offer: None, // No active draw offer initially
            pending_draw_offer: None, // No pending draw offer initially
        }
    }

    /// Resets the turn timer by recording the current `Instant`.
    /// Called at the beginning of each player's turn.
    fn start_turn_timer(&mut self) {
        self.turn_start_time = Some(Instant::now());
    }

     // --- Bitboard Move Generation (Pseudo-Legal) ---

    /// Generates a list of all *pseudo-legal* moves for the player whose turn it is
    /// in the given `state`.
    ///
    /// "Pseudo-legal" means the moves follow the basic movement rules for each piece type
    /// (how they move, captures, pawn pushes, en passant structure, castling structure)
    /// but **does not** check for legality concerning checks (whether the move leaves the
    /// king in check, or attempts to castle through/out of check). Pin checks are also
    /// handled later in `generate_legal_moves`.
    ///
    /// Moves are generated piece by piece and include flags like `is_capture`.
    /// Basic move ordering (captures first) is applied.
    ///
    /// # Parameters
    /// * `state`: The `BitboardState` for which to generate moves.
    /// # Returns
    /// A `Vec<Move>` containing all pseudo-legal moves.
    fn generate_pseudo_legal_moves(&self, state: &BitboardState) -> Vec<Move> {
        let mut moves = Vec::with_capacity(48); // Pre-allocate reasonable capacity
        let color = state.turn; // The player whose turn it is
        let opp_occupied = state.occupied_by_color(color.opponent()); // Squares occupied by the opponent
        let own_occupied = state.occupied_by_color(color); // Squares occupied by the current player
        let occupied = state.occupied; // Squares occupied by any piece

        // Iterate through piece types. Ordering can affect performance in search algorithms
        // (e.g., generating captures or checks first). King first often helps with castling checks.
        for piece_type in [PieceType::King, PieceType::Pawn, PieceType::Knight, PieceType::Bishop, PieceType::Rook, PieceType::Queen] {
            // Get the bitboard for the current piece type and color
            let mut board = state.get_piece_board(piece_type, color);
            // Iterate through each piece of the current type on the board
            while board != 0 {
                let from_sq = board.trailing_zeros() as u8; // Find the square index of the piece
                // Generate moves for this specific piece
                self.generate_moves_for_piece(state, from_sq, piece_type, color, own_occupied, opp_occupied, occupied, &mut moves);
                board &= board - 1; // Clear the bit for the processed piece to move to the next one
            }
        }

        // Simple Move Ordering: Sort moves to place captures before non-captures.
        // This can improve alpha-beta search efficiency by checking likely better moves first.
        // `!mv.is_capture` makes `true` (captures) sort before `false` (non-captures).
        moves.sort_by_key(|mv| !mv.is_capture);

        moves
    }

    /// Generates pseudo-legal moves for a single piece of a specific `piece_type`
    /// located at `from_sq`. Delegates to piece-specific generation functions.
    /// This is a helper function called by `generate_pseudo_legal_moves`.
    ///
    /// # Parameters
    /// * `state`: The current board state.
    /// * `from_sq`: The starting square index (0-63) of the piece.
    /// * `piece_type`: The type of the piece being moved.
    /// * `color`: The color of the piece being moved.
    /// * `own_occupied`: Bitboard of squares occupied by the moving player's pieces.
    /// * `opp_occupied`: Bitboard of squares occupied by the opponent's pieces.
    /// * `occupied`: Bitboard of all occupied squares.
    /// * `moves`: A mutable vector to which generated moves will be added.
    #[inline]
    fn generate_moves_for_piece(&self, state: &BitboardState, from_sq: u8, piece_type: PieceType, color: Color, own_occupied: u64, opp_occupied: u64, occupied: u64, moves: &mut Vec<Move>) {
        match piece_type {
            PieceType::Pawn => self.generate_pawn_moves(state, from_sq, color, opp_occupied, occupied, moves),
            PieceType::Knight => self.generate_knight_moves(from_sq, own_occupied, opp_occupied, moves),
            PieceType::Bishop => self.generate_sliding_moves(from_sq, own_occupied, opp_occupied, occupied, true, false, moves), // Diagonal only
            PieceType::Rook => self.generate_sliding_moves(from_sq, own_occupied, opp_occupied, occupied, false, true, moves), // Orthogonal only
            PieceType::Queen => self.generate_sliding_moves(from_sq, own_occupied, opp_occupied, occupied, true, true, moves), // Both diagonal and orthogonal
            PieceType::King => self.generate_king_moves(state, from_sq, color, own_occupied, opp_occupied, occupied, moves),
        }
    }

     /// Generates pseudo-legal pawn moves from a given square.
     /// Handles single pushes, double pushes (setting EP target implicitly),
     /// regular captures, en passant captures, and promotions.
     /// Sets the `is_capture` flag correctly for both regular and EP captures.
     ///
     /// # Parameters (Similar to `generate_moves_for_piece`)
     /// * `state`: Current board state (needed for EP target square).
     /// * `from_sq`: Starting square of the pawn.
     /// * `color`: Color of the pawn.
     /// * `opp_occupied`: Opponent's occupied squares.
     /// * `occupied`: All occupied squares.
     /// * `moves`: Vector to add generated moves to.
     #[inline]
     fn generate_pawn_moves(&self, state: &BitboardState, from_sq: u8, color: Color, opp_occupied: u64, occupied: u64, moves: &mut Vec<Move>) {
        let from_bb = 1u64 << from_sq; // Bitboard for the starting square
        let empty_squares = !occupied; // Bitboard of all empty squares

        // Determine direction, offsets, and relevant ranks based on pawn color
        let (push_one_offset, // Offset for single square push (+8 for White, -8 for Black)
             push_two_offset, // Offset for double square push (+16 for White, -16 for Black)
             capture_left_offset, // Offset for capture to the left (+7 W, -9 B)
             capture_right_offset,// Offset for capture to the right (+9 W, -7 B)
             promotion_rank_mask, // Bitmask for the promotion rank (Rank 8 for W, Rank 1 for B)
             start_rank_mask,     // Bitmask for the pawn's starting rank (Rank 2 for W, Rank 7 for B)
             ep_capture_rank_mask // Bitmask for the rank FROM which an EP capture is made (Rank 5 W, Rank 4 B)
            ) =
            if color == Color::White {
                // White moves forward (increasing index)
                (8i8, 16i8, 7i8, 9i8, RANK_8, RANK_2, RANK_5)
            } else {
                // Black moves forward (decreasing index)
                (-8i8, -16i8, -9i8, -7i8, RANK_1, RANK_7, RANK_4)
            };

        // 1. Single Pawn Push
        let target_sq_one_signed = from_sq as i8 + push_one_offset; // Calculate potential target square
        if (0..64).contains(&target_sq_one_signed) { // Check if target is on the board
            let target_sq_one = target_sq_one_signed as u8;
            let target_bb_one = 1u64 << target_sq_one;
            // Check if the target square is empty
            if target_bb_one & empty_squares != 0 {
                // Check if this push reaches the promotion rank
                if target_bb_one & promotion_rank_mask != 0 {
                    // If yes, add all possible promotion moves (Queen, Rook, Bishop, Knight)
                    self.add_promotions(from_sq, target_sq_one, false, moves); // is_capture = false
                } else {
                    // If not a promotion, add the single push move
                    moves.push(Move::new(from_sq, target_sq_one, None, false)); // is_capture = false
                }

                // 2. Double Pawn Push (Only possible if single push is valid AND pawn is on its start rank)
                if from_bb & start_rank_mask != 0 {
                    let target_sq_two_signed = from_sq as i8 + push_two_offset;
                    // We already know the first square is clear and the pawn is on the start rank.
                    // Check if the second square is on the board.
                    if (0..64).contains(&target_sq_two_signed) {
                         let target_sq_two = target_sq_two_signed as u8;
                         let target_bb_two = 1u64 << target_sq_two;
                         // Check if the second square ahead is also empty
                         if target_bb_two & empty_squares != 0 {
                            // Add the double push move. Note: This move implicitly sets the EP target square
                            // in the `apply_move` functions later.
                            moves.push(Move::new(from_sq, target_sq_two, None, false)); // is_capture = false
                        }
                    }
                }
            }
        }

        // 3. Pawn Captures (Regular and En Passant)
        for capture_offset in [capture_left_offset, capture_right_offset] {
            // Prevent captures wrapping around the board edge (e.g., pawn on a-file capturing left)
            if (capture_offset == 7 || capture_offset == -9) && (from_bb & FILE_A != 0) { continue; } // Cannot capture left from File A
            if (capture_offset == 9 || capture_offset == -7) && (from_bb & FILE_H != 0) { continue; } // Cannot capture right from File H

            let target_sq_cap_signed = from_sq as i8 + capture_offset; // Calculate potential capture square
            if (0..64).contains(&target_sq_cap_signed) { // Check if target is on the board
                let target_sq_cap = target_sq_cap_signed as u8;
                let target_bb_cap = 1u64 << target_sq_cap;

                // Regular Capture: Check if the target square is occupied by an opponent piece
                if target_bb_cap & opp_occupied != 0 {
                    // Check if this capture results in a promotion
                    if target_bb_cap & promotion_rank_mask != 0 {
                        self.add_promotions(from_sq, target_sq_cap, true, moves); // is_capture = true
                    } else {
                        // Add regular capture move
                        moves.push(Move::new(from_sq, target_sq_cap, None, true)); // is_capture = true
                    }
                }
                // En Passant Capture:
                // Conditions: Pawn must be on the correct rank for EP capture (rank 5 for W, rank 4 for B),
                // AND the target square must match the game state's `en_passant_square`.
                 else if (from_bb & ep_capture_rank_mask != 0) && Some(target_sq_cap) == state.en_passant_square {
                     // Add the en passant move. Mark it as a capture (`is_capture = true`) even though
                     // the target square itself is empty. The actual captured pawn is removed later.
                     // Legality regarding discovered checks is handled in `generate_legal_moves`.
                     moves.push(Move::new(from_sq, target_sq_cap, None, true)); // is_capture = true
                 }
            }
        }
    }

     /// Helper function to add all four possible promotion moves (Q, R, B, N)
     /// for a pawn reaching the back rank.
     /// # Parameters
     /// * `from_sq`: Starting square of the pawn.
     /// * `to_sq`: Destination square (on the promotion rank).
     /// * `is_capture`: Whether the move to the promotion square was a capture.
     /// * `moves`: Vector to add the promotion moves to.
     #[inline]
     fn add_promotions(&self, from_sq: u8, to_sq: u8, is_capture: bool, moves: &mut Vec<Move>) {
        // Add Queen promotion first, as it's the most common (potential minor optimization for search).
        moves.push(Move::new(from_sq, to_sq, Some(PieceType::Queen), is_capture));
        moves.push(Move::new(from_sq, to_sq, Some(PieceType::Knight), is_capture)); // Knight underpromotion is common.
        moves.push(Move::new(from_sq, to_sq, Some(PieceType::Rook), is_capture));
        moves.push(Move::new(from_sq, to_sq, Some(PieceType::Bishop), is_capture));
    }

     /// Generates pseudo-legal knight moves from a given square using the precomputed attack table.
     /// Filters out moves that land on squares occupied by friendly pieces.
     /// Sets the `is_capture` flag if the move lands on an opponent's piece.
     /// # Parameters
     /// * `from_sq`: Starting square of the knight.
     /// * `own_occupied`: Bitboard of squares occupied by the moving player's pieces.
     /// * `opp_occupied`: Bitboard of squares occupied by the opponent's pieces.
     /// * `moves`: Vector to add generated moves to.
     #[inline]
     fn generate_knight_moves(&self, from_sq: u8, own_occupied: u64, opp_occupied: u64, moves: &mut Vec<Move>) {
        // Get the precomputed potential moves for a knight on from_sq
        let potential_moves = KNIGHT_ATTACKS[from_sq as usize];
        // Filter out moves landing on squares occupied by own pieces
        let valid_moves = potential_moves & !own_occupied;

        // Iterate through the set bits (valid destination squares) in the filtered move bitboard
        let mut results = valid_moves;
        while results != 0 {
            let to_sq = results.trailing_zeros() as u8; // Get the index of the destination square
            let target_bb = 1u64 << to_sq;
            // Check if the destination square contains an opponent's piece
            let is_capture = (target_bb & opp_occupied) != 0;
            // Add the knight move
            moves.push(Move::new(from_sq, to_sq, None, is_capture));
            results &= results - 1; // Clear the least significant bit to move to the next destination
        }
    }

    /// Generates pseudo-legal King moves from a given square.
    /// Includes standard one-square moves (using precomputed attacks) and
    /// basic castling moves based *only* on castling rights and whether the squares
    /// between the king and rook are empty.
    /// **Does not** check if the king is in check, moves into check, or castles through check.
    /// These legality checks are handled in `generate_legal_moves`.
    /// Sets `is_capture` flag for standard moves. Castling moves use `Move::new_castle`.
    /// # Parameters
    /// * `state`: Current board state (needed for castling rights and rook positions).
    /// * `from_sq`: Starting square of the king.
    /// * `color`: Color of the king.
    /// * `own_occupied`: Own occupied squares.
    /// * `opp_occupied`: Opponent's occupied squares.
    /// * `occupied`: All occupied squares.
    /// * `moves`: Vector to add generated moves to.
    #[inline]
    fn generate_king_moves(&self, state: &BitboardState, from_sq: u8, color: Color, own_occupied: u64, opp_occupied: u64, occupied: u64, moves: &mut Vec<Move>) {
        // 1. Standard King Moves (non-castling)
        let potential_moves = KING_ATTACKS[from_sq as usize]; // Get precomputed adjacent squares
        let valid_moves = potential_moves & !own_occupied; // Filter out moves to own occupied squares

        // Iterate through valid destinations
        let mut results = valid_moves;
        while results != 0 {
            let to_sq = results.trailing_zeros() as u8;
            let target_bb = 1u64 << to_sq;
            let is_capture = (target_bb & opp_occupied) != 0; // Check if it's a capture
            moves.push(Move::new(from_sq, to_sq, None, is_capture)); // Add the standard move
            results &= results - 1; // Move to next destination
        }

        // 2. Castling Moves (Pseudo-Legal Generation)
        // Get relevant castling parameters based on king's color
        let (can_kside, can_qside, // Castling rights flags
             kside_empty_mask, // Bitmask of squares that must be empty for Kingside castle
             qside_empty_mask, // Bitmask of squares that must be empty for Queenside castle
             kside_rook_sq, // Starting square of the Kingside rook
             qside_rook_sq, // Starting square of the Queenside rook
             kside_target_sq, // King's destination square for Kingside castle
             qside_target_sq // King's destination square for Queenside castle
            ) =
            if color == Color::White {
                (state.castling_rights.white_kingside, state.castling_rights.white_queenside,
                 (1 << 5) | (1 << 6), // f1, g1 must be empty
                 (1 << 1) | (1 << 2) | (1 << 3), // b1, c1, d1 must be empty
                 WHITE_KS_ROOK_START, WHITE_QS_ROOK_START, // h1, a1
                 WHITE_KING_KS_CASTLE_DEST, WHITE_KING_QS_CASTLE_DEST) // g1, c1
            } else { // Black
                (state.castling_rights.black_kingside, state.castling_rights.black_queenside,
                 ((1 << 5) | (1 << 6)) << 56, // f8, g8 must be empty
                 ((1 << 1) | (1 << 2) | (1 << 3)) << 56, // b8, c8, d8 must be empty
                 BLACK_KS_ROOK_START, BLACK_QS_ROOK_START, // h8, a8
                 BLACK_KING_KS_CASTLE_DEST, BLACK_KING_QS_CASTLE_DEST) // g8, c8
            };

        // Get the bitboard for rooks of the current color
        let rook_board = state.get_piece_board(PieceType::Rook, color);

        // Check Kingside Castling
        if can_kside // Check if castling right exists
           && (rook_board & (1 << kside_rook_sq) != 0) // Check if the rook is still on its starting square
           && (occupied & kside_empty_mask == 0) // Check if squares between king and rook are empty
           {
            // Add the Kingside castling move using the special constructor.
            // Legality checks (king not in check, doesn't pass through check) happen later.
            moves.push(Move::new_castle(from_sq, kside_target_sq));
        }

        // Check Queenside Castling
         if can_qside // Check if castling right exists
            && (rook_board & (1 << qside_rook_sq) != 0) // Check if the rook is still on its starting square
            && (occupied & qside_empty_mask == 0) // Check if squares between king and rook are empty
            {
            // Add the Queenside castling move. Legality checks happen later.
            moves.push(Move::new_castle(from_sq, qside_target_sq));
        }
    }

    /// Generates pseudo-legal moves for sliding pieces (Rook, Bishop, Queen) from `from_sq`.
    /// Iterates outwards in each allowed direction (diagonal, orthogonal, or both)
    /// until it hits the edge of the board, a friendly piece (stop before it),
    /// or an enemy piece (include capture move, then stop).
    /// Sets the `is_capture` flag appropriately.
    /// # Parameters
    /// * `from_sq`: Starting square of the sliding piece.
    /// * `own_occupied`: Bitboard of friendly pieces.
    /// * `opp_occupied`: Bitboard of opponent pieces.
    /// * `occupied`: Bitboard of all pieces.
    /// * `diagonals`: Generate moves along diagonals? (True for Bishop, Queen)
    /// * `orthogonals`: Generate moves along ranks/files? (True for Rook, Queen)
    /// * `moves`: Vector to add generated moves to.
    #[inline]
    fn generate_sliding_moves(&self, from_sq: u8, own_occupied: u64, opp_occupied: u64, occupied: u64, diagonals: bool, orthogonals: bool, moves: &mut Vec<Move>) {
        // Iterate through the 8 directions (defined in `DIRECTIONS` constant)
        for &(dr, df, is_diagonal) in DIRECTIONS {
            // Check if this direction is relevant based on piece type (diagonal/orthogonal flags)
            if (diagonals && is_diagonal) || (orthogonals && !is_diagonal) {
                // Start from the piece's square
                let mut current_rank = (from_sq / 8) as i8;
                let mut current_file = (from_sq % 8) as i8;

                // Move step-by-step along the ray in the current direction
                loop {
                    current_rank += dr; // Move one step in rank
                    current_file += df; // Move one step in file

                    // Check if the new square is off the board
                    if !(0..8).contains(&current_rank) || !(0..8).contains(&current_file) {
                        break; // Stop searching in this direction
                    }

                    let next_sq = (current_rank * 8 + current_file) as u8; // Calculate square index
                    let next_bb = 1u64 << next_sq; // Bitboard for the target square

                    // Check if the target square is occupied by a friendly piece
                    if next_bb & own_occupied != 0 {
                        break; // Blocked by own piece, stop searching in this direction
                    }

                    // Check if the target square is occupied by an opponent's piece (capture)
                    let is_capture = (next_bb & opp_occupied) != 0;
                    // Add the move (either quiet move to empty square or capture)
                    moves.push(Move::new(from_sq, next_sq, None, is_capture));

                    // If the square was occupied (either friendly or enemy), stop searching further
                    // along this ray after adding the move (if it was a capture).
                    // This also handles the case where `next_bb & own_occupied != 0` caused an early break.
                    if next_bb & occupied != 0 {
                        break;
                    }
                    // If the square was empty, continue along the ray.
                }
            }
        }
    }

     // --- Attack Generation ---

    /// Checks if a given square (`target_sq`) is attacked by any piece of the `attacker_color`.
    /// This function considers the raw attack patterns of all piece types, ignoring pins
    /// and whether the attacking move would be legal (e.g., it doesn't check if moving
    /// the attacker would expose their own king). Used primarily for check detection
    /// and king move legality checks.
    /// # Parameters
    /// * `state`: The current board state.
    /// * `target_sq`: The square index (0-63) to check for attacks.
    /// * `attacker_color`: The color of the pieces potentially attacking the square.
    /// # Returns
    /// `true` if the square is attacked by at least one piece of `attacker_color`, `false` otherwise.
    fn is_square_attacked(&self, state: &BitboardState, target_sq: u8, attacker_color: Color) -> bool {
        let occupied = state.occupied; // Combined occupancy needed for sliding piece checks

        // 1. Check for Pawn Attacks
        let pawn_board = state.get_piece_board(PieceType::Pawn, attacker_color);
        if pawn_board != 0 { // Optimization: only check if pawns exist
            // Determine the relative offsets FROM which a pawn could attack the target square
            let (cap_l_off, cap_r_off) = if attacker_color == Color::White {
                // If White is attacking, look for white pawns one step South-West (-9) or South-East (-7) of the target
                (-9i8, -7i8)
            } else {
                // If Black is attacking, look for black pawns one step North-West (+7) or North-East (+9) of the target
                (7i8, 9i8)
            };

            let target_bb = 1u64 << target_sq; // Bitboard for the target square

            // Check potential attacking square to the 'left' (SW for White, NW for Black)
            // Ensure the target square is not on File A before checking left attack
            if target_bb & NOT_FILE_A != 0 {
                let pot_att_sq_l_signed = target_sq as i8 + cap_l_off;
                 // Check if potential attacker square is on the board
                 if (0..64).contains(&pot_att_sq_l_signed) {
                     // Check if an attacker pawn exists on that square
                     if (pawn_board & (1u64 << pot_att_sq_l_signed)) != 0 { return true; }
                 }
            }
            // Check potential attacking square to the 'right' (SE for White, NE for Black)
            // Ensure the target square is not on File H before checking right attack
            if target_bb & NOT_FILE_H != 0 {
                let pot_att_sq_r_signed = target_sq as i8 + cap_r_off;
                 // Check if potential attacker square is on the board
                 if (0..64).contains(&pot_att_sq_r_signed) {
                     // Check if an attacker pawn exists on that square
                     if (pawn_board & (1u64 << pot_att_sq_r_signed)) != 0 { return true; }
                 }
            }
        }

        // 2. Check for Knight Attacks (using precomputed table)
        let knight_board = state.get_piece_board(PieceType::Knight, attacker_color);
        // Check if any knight of the attacker color exists on a square that attacks the target square
        if knight_board != 0 && (KNIGHT_ATTACKS[target_sq as usize] & knight_board) != 0 { return true; }

        // 3. Check for King Attacks (using precomputed table)
        let king_board = state.get_piece_board(PieceType::King, attacker_color);
        // Check if the attacker's king is on a square that attacks the target square
        if king_board != 0 && (KING_ATTACKS[target_sq as usize] & king_board) != 0 { return true; }

        // 4. Check for Sliding Piece Attacks (Rooks, Bishops, Queens)
        let rook_board = state.get_piece_board(PieceType::Rook, attacker_color);
        let bishop_board = state.get_piece_board(PieceType::Bishop, attacker_color);
        let queen_board = state.get_piece_board(PieceType::Queen, attacker_color);

        // Check Orthogonal attacks (Rooks or Queens)
        let orth_attackers = rook_board | queen_board; // Combine rooks and queens
        if orth_attackers != 0 {
            // Generate all squares attacked orthogonally *from* target_sq, considering blockers
            let orth_attacks = self.get_sliding_attacks(target_sq, occupied, false, true);
            // Check if any actual orthogonal attacker sits on one of these attack lines
            if orth_attacks & orth_attackers != 0 { return true; }
        }

        // Check Diagonal attacks (Bishops or Queens)
        let diag_attackers = bishop_board | queen_board; // Combine bishops and queens
        if diag_attackers != 0 {
            // Generate all squares attacked diagonally *from* target_sq, considering blockers
            let diag_attacks = self.get_sliding_attacks(target_sq, occupied, true, false);
            // Check if any actual diagonal attacker sits on one of these attack lines
            if diag_attacks & diag_attackers != 0 { return true; }
        }

        // If no attacks found from any piece type
        false
    }


    /// Checks if the king of the specified `color` is currently in check.
    /// Finds the king's square and then calls `is_square_attacked` by the opponent.
    /// # Parameters
    /// * `state`: The current board state.
    /// * `color`: The color of the king to check.
    /// # Returns
    /// `true` if the king of the specified color is in check, `false` otherwise.
    /// Returns `true` and prints an error if the king cannot be found (indicates corrupt state).
    #[inline]
    fn is_in_check(&self, state: &BitboardState, color: Color) -> bool {
        match state.find_king(color) {
            Some(king_sq) => {
                // Check if the king's square is attacked by the opponent
                self.is_square_attacked(state, king_sq, color.opponent())
            }
            None => {
                // This should ideally never happen in a valid game.
                eprintln!("CRITICAL ERROR: King of color {:?} not found in bitboard state! State:\n{:?}", color, state);
                // Returning true might be safer than false if the state is corrupt,
                // as it prevents illegal moves assuming the king is safe.
                true
            }
        }
    }

    // --- Pin Detection ---

    /// Computes which pieces of the given `color` are absolutely pinned to their king.
    /// An absolute pin occurs when a piece lies on a line (rank, file, or diagonal)
    /// between its own king and an attacking enemy slider (Rook, Bishop, or Queen).
    /// The pinned piece can only move along the line of the pin or capture the pinning piece.
    ///
    /// # Parameters
    /// * `state`: The current board state.
    /// * `color`: The color of the player whose pieces might be pinned.
    /// # Returns
    /// A `PinInfo` struct containing:
    ///   - `pinned_pieces`: A bitboard of the squares occupied by pinned friendly pieces.
    ///   - `pin_restriction_map`: An array where `map[sq]` gives the allowed move squares
    ///     (along the pin ray) if the piece on `sq` is pinned.
    fn compute_pins(&self, state: &BitboardState, color: Color) -> PinInfo {
        // Find the king's square first. If no king, no pins are possible.
        let king_sq = match state.find_king(color) {
            Some(sq) => sq,
            None => return PinInfo::default(), // Return empty PinInfo if king not found
        };

        let mut pin_info = PinInfo::default(); // Initialize result
        let own_occupied = state.occupied_by_color(color); // Friendly pieces
        let opp_color = color.opponent(); // Opponent's color
        // Bitboards of opponent's sliding pieces capable of pinning
        let opp_rooks_queens = state.get_piece_board(PieceType::Rook, opp_color) | state.get_piece_board(PieceType::Queen, opp_color);
        let opp_bishops_queens = state.get_piece_board(PieceType::Bishop, opp_color) | state.get_piece_board(PieceType::Queen, opp_color);
        let occupied = state.occupied; // All occupied squares

        // Iterate through the 8 directions radiating from the king
        for &(dr, df, is_diagonal) in DIRECTIONS {
            // Determine which type of opponent slider could potentially pin along this direction
            let potential_pinners = if is_diagonal { opp_bishops_queens } else { opp_rooks_queens };
            // Optimization: If no relevant opponent sliders exist, skip this direction.
            if potential_pinners == 0 { continue; }

            let mut ray_mask: u64 = 0; // Tracks squares along the current ray *including* potential pinner
            let mut potential_pinned_sq: Option<u8> = None; // Tracks the first friendly piece found along the ray
            let mut current_rank = (king_sq / 8) as i8; // Start scan from king's position
            let mut current_file = (king_sq % 8) as i8;

            // Scan along the ray, step by step
            loop {
                current_rank += dr;
                current_file += df;

                // Stop if we go off the board
                if !(0..8).contains(&current_rank) || !(0..8).contains(&current_file) { break; }
                let next_sq = (current_rank * 8 + current_file) as u8;
                let next_bb = 1u64 << next_sq;

                ray_mask |= next_bb; // Add the current square to the ray mask being built

                // Check if the current square along the ray is occupied
                if next_bb & occupied != 0 {
                    // Found a piece. Is it friendly or opponent?
                    if next_bb & own_occupied != 0 { // Found a friendly piece
                        if potential_pinned_sq.is_none() {
                            // This is the *first* friendly piece along this ray. It's potentially pinned.
                            potential_pinned_sq = Some(next_sq);
                        } else {
                            // Found a *second* friendly piece along the ray. The first one acts as a blocker,
                            // so no pin is possible along this ray. Stop scanning this direction.
                            break;
                        }
                    } else { // Found an opponent piece
                        if let Some(pinned_sq) = potential_pinned_sq {
                            // We previously found exactly one friendly piece between the king and this opponent piece.
                            // Now, check if this opponent piece is a relevant slider (R/Q or B/Q).
                            if next_bb & potential_pinners != 0 {
                                // Yes! The friendly piece at `pinned_sq` is absolutely pinned.
                                pin_info.pinned_pieces |= 1u64 << pinned_sq; // Mark the piece as pinned
                                // The pinned piece can only move along the ray (including capturing the pinner).
                                // Store the ray mask as the restriction for this pinned piece.
                                pin_info.pin_restriction_map[pinned_sq as usize] = ray_mask;
                            }
                        }
                        // Whether this opponent piece was a pinner or just a blocker,
                        // stop scanning further along this ray.
                        break;
                    }
                }
                // If the square was empty, continue scanning along the ray.
            }
        }
        pin_info // Return the computed pin information
    }


    // --- Legal Move Generation (Incorporating Pins and Checks) ---

    /// Generates a list of all *fully legal* moves for the player whose turn it is
    /// in the given `state`.
    /// This involves:
    /// 1. Generating pseudo-legal moves.
    /// 2. Checking if the king is currently in check.
    /// 3. Computing which pieces are pinned.
    /// 4. Filtering pseudo-legal moves based on check and pin restrictions:
    ///    - King cannot move into check.
    ///    - Cannot castle out of, through, or into check.
    ///    - Pinned pieces can only move along the pin ray (or capture the pinner).
    ///    - If in check, the move must resolve the check (capture attacker, block, or move king).
    ///    - En passant captures must be checked for discovered checks.
    /// Uses `apply_move_immutable_no_zobrist` to simulate moves for complex legality checks.
    /// # Parameters
    /// * `state`: The `BitboardState` for which to generate legal moves.
    /// # Returns
    /// A `Vec<Move>` containing only the fully legal moves.
    fn generate_legal_moves(&self, state: &BitboardState) -> Vec<Move> {
        let mut legal_moves = Vec::with_capacity(48); // Pre-allocate
        let color = state.turn; // Player to move
        let opp_color = color.opponent();

        // Find the player's king. If missing, return empty list (error state).
        let king_sq = match state.find_king(color) {
            Some(sq) => sq,
            None => {
                 eprintln!("ERROR in generate_legal_moves: King for {:?} not found!", color);
                 return legal_moves;
            }
        };

        // 1. Compute Pins and Squares Attacked by Opponent
        let pin_info = self.compute_pins(state, color); // Identify pinned pieces for 'color'
        let attacked_by_opponent = self.compute_attack_map(state, opp_color); // Map of all squares opponent attacks

        // 2. Check if the King is currently in check
        let is_king_in_check = (attacked_by_opponent & (1u64 << king_sq)) != 0;

        // 3. Generate all Pseudo-Legal Moves first
        let pseudo_legal_moves = self.generate_pseudo_legal_moves(state);

        // 4. Filter Pseudo-Legal Moves for Full Legality
        for mv in pseudo_legal_moves {
            let from_bb = 1u64 << mv.from_sq;
            // Get the type of the piece being moved (used for king/pawn special checks)
            let moving_piece_type = state.get_piece_at(mv.from_sq).map(|p| p.kind);

            // --- A. Handle King Moves (including Castling) ---
            if moving_piece_type == Some(PieceType::King) {
                 // A.1: Regular King Move Legality: Cannot move into an attacked square.
                 // Check if the destination square `mv.to_sq` is attacked by the opponent.
                 if (attacked_by_opponent & (1u64 << mv.to_sq)) != 0 {
                     continue; // Illegal move: King would land in check.
                 }

                 // A.2: Castling Legality Checks (only if the move is flagged as castle)
                 if mv.is_castle {
                      // Rule 1: Cannot castle if the king is currently in check.
                      if is_king_in_check { continue; }

                      // Rule 2: King cannot pass *through* an attacked square.
                      // Determine the square(s) the king passes over.
                      let pass_sq_1; // The square immediately adjacent to the king (f1/d1 or f8/d8)
                      if mv.to_sq > mv.from_sq { // Kingside castle (e.g. e1 -> g1)
                          pass_sq_1 = mv.from_sq + 1; // f1 / f8
                      } else { // Queenside castle (e.g. e1 -> c1)
                          pass_sq_1 = mv.from_sq - 1; // d1 / d8
                          // Queenside also requires checking the b-file square (c1/c8 is landing square)
                          let pass_sq_b_file = mv.from_sq - 2; // b1 / b8
                          if (attacked_by_opponent & (1u64 << pass_sq_b_file)) != 0 {
                              continue; // Illegal: King passes through check on b-file square.
                          }
                      }

                     // Check if the first square the king passes over (f1/d1 or f8/d8) is attacked.
                     if (attacked_by_opponent & (1u64 << pass_sq_1)) != 0 {
                         continue; // Illegal: King passes through check.
                     }
                     // Rule 3 (King cannot land in check) was already checked above for all king moves.

                     // If all castling checks passed, the move is legal (fall through).
                }

                // If we reach here, the king move (regular or castling) is legal regarding checks.
                // Add it to the list. No need to simulate the move, as we checked destination/path attacks directly.
                legal_moves.push(mv);
            }
            // --- B. Handle Non-King Moves ---
            else {
                 // B.1: Check Pin Restrictions
                 // Is the moving piece pinned?
                 let is_pinned = (from_bb & pin_info.pinned_pieces) != 0;
                 if is_pinned {
                      // If pinned, the move MUST be along the pin line (or capture the pinner).
                      // Get the allowed movement mask for this pinned piece.
                      let allowed_move_mask = pin_info.pin_restriction_map[mv.from_sq as usize];
                      // Check if the destination square is within the allowed mask.
                      if ((1u64 << mv.to_sq) & allowed_move_mask) == 0 {
                          continue; // Illegal move: Pinned piece moving off the pin line.
                      }
                      // If the move is along the pin line, it *might* be legal (still need check validation below).
                 }

                 // B.2: Special Check for En Passant Discovered Check
                 // En passant is the only move where a piece moves to an empty square but removes
                 // a piece from a *different* square, potentially revealing a check.
                 // Identify EP capture: pawn move, target matches EP square, capture flag is set, target is empty.
                 let is_ep_capture = moving_piece_type == Some(PieceType::Pawn) &&
                                    Some(mv.to_sq) == state.en_passant_square &&
                                    mv.is_capture && // Use the capture flag set during pseudo-legal generation
                                    state.get_piece_at(mv.to_sq).is_none(); // Target must be empty for EP

                 if is_ep_capture {
                     // Must simulate the EP capture to see if it leaves the king in check.
                     match self.apply_move_immutable_no_zobrist(state, &mv) {
                         Ok((next_state, _)) => {
                             // After the EP capture, is the current player's king safe?
                             if !self.is_in_check(&next_state, color) {
                                 // Yes, the EP capture is fully legal.
                                 legal_moves.push(mv);
                             }
                             // else: Illegal EP capture due to discovered check. Do not add the move.
                         },
                         Err(e) => {
                             // This indicates an internal error in the pseudo-legal or simulation logic.
                             eprintln!("Internal error simulating EP capture for {:?}: {}", mv.to_algebraic_string(), e);
                         }
                     }
                 } else {
                     // B.3: General Legality Check for Non-King, Non-EP moves

                     // If the king IS in check, *any* legal move MUST resolve the check
                     // (by moving king, capturing attacker, or blocking).
                     // If the king is NOT in check, the move must NOT expose the king to check.
                     // The pin check (B.1) handles most cases of exposing the king.

                     // Optimization: If the king is NOT currently in check AND the moving piece is NOT pinned,
                     // then any pseudo-legal move (that isn't EP) is guaranteed to be legal.
                     // This is because non-pinned pieces cannot expose the king by moving.
                     if !is_king_in_check && !is_pinned {
                         legal_moves.push(mv);
                     } else {
                         // We must verify legality by simulation in these cases:
                         // - King is currently in check (move must resolve it).
                         // - King is not in check, but a pinned piece is moving along its pin line
                         //   (this is generally legal, but simulation confirms no edge cases).
                         match self.apply_move_immutable_no_zobrist(state, &mv) {
                             Ok((next_state, _captured_piece)) => {
                                 // After the move, is the current player's king safe?
                                 if !self.is_in_check(&next_state, color) {
                                     legal_moves.push(mv); // Move is legal
                                 }
                                 // else: Move is illegal because it doesn't resolve check or exposes king (e.g., impossible edge case)
                             }
                             Err(e) => {
                                 // Indicates an internal error during simulation.
                                 eprintln!("Internal Error during legal move generation (apply_immutable) for {:?}: {}", mv.to_algebraic_string(), e);
                             }
                         }
                     }
                 } // End !is_ep_capture block
            } // End Non-King Moves block
        } // End loop over pseudo_legal_moves

        legal_moves
    }


    /// Computes a bitboard map where each set bit represents a square that is attacked
    /// by at least one piece of the specified `attacker_color`.
    /// This is a crucial helper for check detection and validating king moves.
    /// It aggregates the attack patterns of all pieces of the given color.
    /// # Parameters
    /// * `state`: The current board state.
    /// * `attacker_color`: The color of the pieces whose attacks are being calculated.
    /// # Returns
    /// A `u64` bitboard representing all squares attacked by `attacker_color`.
    fn compute_attack_map(&self, state: &BitboardState, attacker_color: Color) -> u64 {
        let mut attack_map: u64 = 0; // Start with an empty map
        let occupied = state.occupied; // Combined occupancy needed for sliding pieces

        // --- Pawns ---
        let pawn_board = state.get_piece_board(PieceType::Pawn, attacker_color);
        if pawn_board != 0 {
            if attacker_color == Color::White {
                // White pawns attack diagonally forward-left (NW) and forward-right (NE).
                // Shift the pawn bitboard, masking to prevent wrapping.
                attack_map |= (pawn_board & NOT_FILE_A).wrapping_shl(7); // Attack Up-Left
                attack_map |= (pawn_board & NOT_FILE_H).wrapping_shl(9); // Attack Up-Right
            } else { // Black
                // Black pawns attack diagonally forward-left (SW) and forward-right (SE).
                attack_map |= (pawn_board & NOT_FILE_A).wrapping_shr(9); // Attack Down-Left
                attack_map |= (pawn_board & NOT_FILE_H).wrapping_shr(7); // Attack Down-Right
            }
        }

        // --- Knights ---
        let knight_board = state.get_piece_board(PieceType::Knight, attacker_color);
        let mut knights = knight_board;
        // Iterate through each knight on the board
        while knights != 0 {
            let sq = knights.trailing_zeros() as usize; // Get knight's square index
            // Add (OR) the precomputed attacks for this knight to the map
            attack_map |= KNIGHT_ATTACKS[sq];
            knights &= knights - 1; // Clear the bit for this knight
        }

        // --- King ---
        let king_board = state.get_piece_board(PieceType::King, attacker_color);
         if king_board != 0 {
             let sq = king_board.trailing_zeros() as usize; // Get king's square index
             // Add (OR) the precomputed attacks for the king to the map
             attack_map |= KING_ATTACKS[sq];
         }

        // --- Sliding Pieces (Rook, Bishop, Queen) ---
        let rook_board = state.get_piece_board(PieceType::Rook, attacker_color);
        let bishop_board = state.get_piece_board(PieceType::Bishop, attacker_color);
        let queen_board = state.get_piece_board(PieceType::Queen, attacker_color);

        // Rooks & Queens (Orthogonal Attacks)
        let mut rooks_queens = rook_board | queen_board; // Combine R and Q boards
        while rooks_queens != 0 {
            let sq = rooks_queens.trailing_zeros(); // Get slider's square index
            // Calculate sliding attacks from this square, considering blockers (`occupied`)
            attack_map |= self.get_sliding_attacks(sq as u8, occupied, false, true);
            rooks_queens &= rooks_queens - 1; // Clear the bit for this slider
        }

        // Bishops & Queens (Diagonal Attacks)
        let mut bishops_queens = bishop_board | queen_board; // Combine B and Q boards
        while bishops_queens != 0 {
            let sq = bishops_queens.trailing_zeros(); // Get slider's square index
            // Calculate sliding attacks from this square, considering blockers (`occupied`)
            attack_map |= self.get_sliding_attacks(sq as u8, occupied, true, false);
            bishops_queens &= bishops_queens - 1; // Clear the bit for this slider
        }

        attack_map // Return the final combined attack map
    }

     /// Helper function to calculate the attack bitboard for a sliding piece (R, B, Q)
     /// on a given square `from_sq`. It scans outwards in the allowed directions
     /// (`diagonals`, `orthogonals`) and includes all squares reached until a piece
     /// (of either color) is hit. The blocking piece itself *is* included in the attack map.
     /// # Parameters
     /// * `from_sq`: The square index (0-63) of the sliding piece.
     /// * `occupied`: A bitboard representing all occupied squares (both colors). Used for blocking.
     /// * `diagonals`: Include diagonal attacks?
     /// * `orthogonals`: Include orthogonal attacks?
     /// # Returns
     /// A `u64` bitboard representing all squares attacked by the slider from `from_sq`.
     #[inline]
    fn get_sliding_attacks(&self, from_sq: u8, occupied: u64, diagonals: bool, orthogonals: bool) -> u64 {
        let mut attacks: u64 = 0; // Start with empty attack map

        // Iterate through the 8 directions
        for &(dr, df, is_diagonal) in DIRECTIONS {
            // Check if this direction is relevant for the piece type
            if (diagonals && is_diagonal) || (orthogonals && !is_diagonal) {
                // Start scan from the piece's square
                let mut current_rank = (from_sq / 8) as i8;
                let mut current_file = (from_sq % 8) as i8;
                // Scan step-by-step along the ray
                loop {
                    current_rank += dr;
                    current_file += df;

                    // Stop if off board
                    if !(0..8).contains(&current_rank) || !(0..8).contains(&current_file) { break; }
                    let next_sq = (current_rank * 8 + current_file) as u8;
                    let next_bb = 1u64 << next_sq;

                    // Add the current square to the attack map
                    attacks |= next_bb;

                    // If this square is occupied by *any* piece, it blocks further attacks along this ray.
                    if next_bb & occupied != 0 {
                        break; // Stop scanning this direction
                    }
                    // If empty, continue along the ray.
                }
            }
        }
        attacks // Return the combined attacks for all relevant directions
    }

    // --- Immutable Move Application (Helper for generate_legal_moves) ---

    /// Creates a *new* `BitboardState` representing the board after the given `mv` is applied
    /// to the input `state`, without modifying the original `state`.
    /// This is primarily used for legality checking in `generate_legal_moves`, especially
    /// for verifying en passant captures and complex check resolutions.
    ///
    /// **Assumes the input `mv` is pseudo-legal** regarding basic piece movement patterns
    /// (e.g., knight moves like a knight, pawn pushes forward). It does *not* re-validate
    /// things like castling paths being clear or rights existing, relying on the pseudo-legal
    /// generator for that basic structure. It *does* handle the mechanics of moving pieces,
    /// captures (including EP), promotions, castling rook movement, and updating state
    /// variables like turn, clocks, EP target, and castling rights based on the move's effects.
    ///
    /// **Does not update or use Zobrist keys.**
    ///
    /// # Parameters
    /// * `state`: The starting `BitboardState`.
    /// * `mv`: The pseudo-legal `Move` to apply.
    /// # Returns
    /// * `Ok((BitboardState, Option<Piece>))` where `BitboardState` is the resulting state
    ///   and `Option<Piece>` is the piece captured during the move (if any).
    /// * `Err(MoveError)` if an internal inconsistency is detected (e.g., trying to apply
    ///   an EP capture where the captured pawn doesn't exist), indicating a potential bug
    ///   in the pseudo-legal generation or the simulation logic itself.
    fn apply_move_immutable_no_zobrist(&self, state: &BitboardState, mv: &Move) -> Result<(BitboardState, Option<Piece>), MoveError> {
        let mut next_state = state.clone(); // Work on a copy
        let moving_color = state.turn;
        // Find the piece being moved. Should always exist if the move is pseudo-legal.
        let moving_piece = state.get_piece_at(mv.from_sq)
            .ok_or(MoveError::InternalError("Piece not found at 'from' sq in immutable apply"))?;

        let is_pawn_move = moving_piece.kind == PieceType::Pawn;
        let mut castle_rook_move: Option<(u8, u8)> = None; // Stores (rook_from, rook_to) if castling
        let mut temp_zobrist = 0; // Dummy Zobrist key, not used by caller, needed for clear/set signatures
        let mut actual_captured_piece: Option<Piece> = None; // Stores the piece actually captured
        let mut is_capture = false; // Track if any capture occurred (regular or EP)

        // --- Pre-calculate Castling Rook Move ---
        // If the move is a king move flagged as castling
        if moving_piece.kind == PieceType::King && mv.is_castle {
             // Determine rook's start and end squares based on king's destination
             let (rook_from_sq, rook_to_sq) = if mv.to_sq > mv.from_sq { // Kingside (e.g., g1/g8 destination)
                  if moving_color == Color::White { (WHITE_KS_ROOK_START, 5) } // h1 -> f1
                  else { (BLACK_KS_ROOK_START, 61) } // h8 -> f8
              } else { // Queenside (e.g., c1/c8 destination)
                 if moving_color == Color::White { (WHITE_QS_ROOK_START, 3) } // a1 -> d1
                 else { (BLACK_QS_ROOK_START, 59) } // a8 -> d8
              };
              // Sanity check: Does the rook actually exist at the expected starting square in the *current* state?
               if next_state.get_piece_at(rook_from_sq).map_or(true, |p| p.kind != PieceType::Rook || p.color != moving_color) {
                    // This indicates an issue if called with an invalid castling move struct
                    return Err(MoveError::InternalError("Castling error: Rook missing or wrong piece at origin in immutable apply"));
               }
              castle_rook_move = Some((rook_from_sq, rook_to_sq)); // Store rook move details
        }

        // --- Handle En Passant Capture ---
        // Conditions: Pawn move, destination matches state's EP target, destination square is empty
        if is_pawn_move && Some(mv.to_sq) == state.en_passant_square && state.get_piece_at(mv.to_sq).is_none() {
             // Calculate the square of the pawn *actually* being captured (behind the EP target square)
             let captured_pawn_sq_opt = if moving_color == Color::White {
                 mv.to_sq.checked_sub(8) // White captures on rank 6, removes pawn on rank 5
             } else {
                 mv.to_sq.checked_add(8) // Black captures on rank 3, removes pawn on rank 4
             };

             if let Some(cap_sq) = captured_pawn_sq_opt {
                 if cap_sq < 64 { // Ensure valid square index
                     // Clear the captured pawn from its square. Updates `actual_captured_piece`.
                     actual_captured_piece = next_state.clear_square(cap_sq, &mut temp_zobrist);
                     // Sanity check: Was the removed piece actually the opponent's pawn?
                     if actual_captured_piece.map_or(true, |p| p.kind != PieceType::Pawn || p.color == moving_color) {
                          // Log a warning, but maybe proceed depending on strictness needs. Could return Err here.
                          eprintln!("WARN (immutable): EP capture at {} expected opponent pawn at {} but found {:?}.", index_to_algebraic(mv.to_sq), index_to_algebraic(cap_sq), actual_captured_piece);
                     }
                     is_capture = true; // Mark that a capture occurred
                 } else {
                     return Err(MoveError::InternalError("Internal en passant error: Invalid capture square calculated"));
                 }
             } else {
                  return Err(MoveError::InternalError("Internal en passant error: Capture square calculation underflow/overflow"));
             }
        }

        // --- Move the Main Piece ---
        // 1. Clear the piece from its starting square.
        next_state.clear_square(mv.from_sq, &mut temp_zobrist);
        // 2. Clear the destination square. This handles regular captures.
        // If a piece is on `to_sq`, `clear_square` removes it and returns it.
        let captured_on_to_sq = next_state.clear_square(mv.to_sq, &mut temp_zobrist);

        // 3. Update final capture status
        if captured_on_to_sq.is_some() {
            if actual_captured_piece.is_some() {
                 // Error: Should not have both an EP capture and a capture on the destination square.
                 return Err(MoveError::InternalError("Internal error: Both EP capture and direct capture detected"));
            }
             actual_captured_piece = captured_on_to_sq; // Store the captured piece
            is_capture = true; // Mark that a capture occurred
        }

        // 4. Place the moving piece (or promoted piece) on the destination square.
        let piece_to_place_type = mv.promotion.unwrap_or(moving_piece.kind); // Use promotion type if available
        next_state.set_piece_at(mv.to_sq, piece_to_place_type, moving_color, &mut temp_zobrist);


        // --- Handle Castling Rook Move (Piece Movement) ---
        if let Some((rook_from, rook_to)) = castle_rook_move {
            // Remove the rook from its starting square
            next_state.clear_square(rook_from, &mut temp_zobrist);
             // Place the rook on its destination square
             next_state.set_piece_at(rook_to, PieceType::Rook, moving_color, &mut temp_zobrist);
        }

        // --- Update Other State Variables (Castling Rights, EP, Clocks, Turn) ---

        // Castling rights update (start with previous rights, then modify)
        let mut next_castling_rights = state.castling_rights;
        // Rule 1: If King moved, revoke its castling rights.
        if moving_piece.kind == PieceType::King {
            next_castling_rights.king_moved(moving_color);
        }
        // Rule 2: If a Rook moved *from* its starting square, revoke the corresponding right.
        if moving_piece.kind == PieceType::Rook {
             match mv.from_sq {
                 WHITE_QS_ROOK_START if moving_color == Color::White => next_castling_rights.white_queenside = false,
                 WHITE_KS_ROOK_START if moving_color == Color::White => next_castling_rights.white_kingside = false,
                 BLACK_QS_ROOK_START if moving_color == Color::Black => next_castling_rights.black_queenside = false,
                 BLACK_KS_ROOK_START if moving_color == Color::Black => next_castling_rights.black_kingside = false,
                 _ => {} // Rook moved from a different square
             }
        }
        // Rule 3: If a Rook was captured *on* its starting square, revoke the corresponding right.
        if let Some(captured) = actual_captured_piece { // Use the final determined captured piece
            if captured.kind == PieceType::Rook {
                match mv.to_sq { // Check the square where the capture happened
                    WHITE_QS_ROOK_START => next_castling_rights.white_queenside = false, // Opponent captured a1 rook
                    WHITE_KS_ROOK_START => next_castling_rights.white_kingside = false, // Opponent captured h1 rook
                    BLACK_QS_ROOK_START => next_castling_rights.black_queenside = false, // Opponent captured a8 rook
                    BLACK_KS_ROOK_START => next_castling_rights.black_kingside = false, // Opponent captured h8 rook
                    _ => {} // Rook captured on a different square
                 }
            }
        }
        next_state.castling_rights = next_castling_rights; // Update the state's rights

        // En Passant square update
        next_state.en_passant_square = None; // Always reset EP target first
        // If the move was a pawn double push, set the new EP target square
        if is_pawn_move {
            let rank_diff = (mv.to_sq / 8).abs_diff(mv.from_sq / 8); // Calculate rank difference
            if rank_diff == 2 {
                // The EP target is the square the pawn skipped over
                let ep_target_sq = if moving_color == Color::White { mv.from_sq + 8 } else { mv.from_sq - 8 };
                next_state.en_passant_square = Some(ep_target_sq);
            }
        }

        // Halfmove clock update
        // Reset if it was a pawn move or a capture (using the final `is_capture` status).
        if is_pawn_move || is_capture {
            next_state.halfmove_clock = 0;
        } else {
            // Increment if it was neither a pawn move nor a capture.
            next_state.halfmove_clock = state.halfmove_clock + 1;
        }

        // Fullmove number update
        // Increment after Black moves.
         if moving_color == Color::Black {
             next_state.fullmove_number = state.fullmove_number + 1;
         }

        // Switch turn to the opponent
        next_state.turn = moving_color.opponent();
        // Update the aggregate occupancy bitboards to reflect all piece changes
        next_state.update_occupancy();

        Ok((next_state, actual_captured_piece)) // Return the new state and captured piece
    }


    /// Applies a *validated legal* move to the main game state (`self.current_state`),
    /// updating piece positions, state variables (turn, clocks, EP, castling),
    /// and the game's Zobrist key incrementally.
    ///
    /// **Assumes the input `mv` is fully legal** (i.e., it came from `generate_legal_moves`)
    /// and has correct flags (`is_capture`, `is_castle`). It performs the mechanics of the move.
    ///
    /// Updates the Zobrist key by:
    /// 1. XORing out the keys for the previous state components (castling, EP, side-to-move).
    /// 2. Performing piece moves/captures (which XOR piece keys in/out via `clear_square`/`set_piece_at`).
    /// 3. Updating state variables (castling, EP, side-to-move).
    /// 4. XORing in the keys for the *new* state components.
    ///
    /// # Parameters
    /// * `mv`: The legal `Move` to apply.
    /// # Returns
    /// * `Some(Piece)` containing the piece that was captured during the move, if any.
    /// * `None` if the move was not a capture.
    /// # Panics
    /// Panics if called with a move that leads to an inconsistent state (e.g., finding a piece
    /// at the 'from' square that doesn't match expectations, or detecting both EP and direct capture),
    /// as this indicates a flaw in the legal move generation or the `mv` structure itself.
    fn apply_legal_move(&mut self, mv: &Move) -> Option<Piece> {
        let state = &mut self.current_state; // Get mutable reference to the main state
        let moving_color = state.turn;
        // Get the moving piece. Unwrap is used assuming the move is validated legal.
        let moving_piece = state.get_piece_at(mv.from_sq)
            .unwrap_or_else(|| panic!("apply_legal_move called with empty 'from' square: {}", index_to_algebraic(mv.from_sq)));

        // --- Zobrist Key: Start Incremental Update ---
        // Store the current key. We will modify this copy and assign it back at the end.
        let mut current_zobrist_key = self.zobrist_key;
        // 1. XOR out keys for state components that are about to change.
        current_zobrist_key ^= ZOBRIST.castling(state.castling_rights); // Old castling rights
        current_zobrist_key ^= ZOBRIST.en_passant(state.en_passant_square); // Old EP target
        current_zobrist_key ^= ZOBRIST.side_to_move(state.turn); // Old side to move

        // --- State Update ---
        // Use flags from the validated `Move` struct.
        let mut is_capture = mv.is_capture; // Assume the flag is correct for a legal move
        let is_pawn_move = moving_piece.kind == PieceType::Pawn;
        let mut castle_rook_move: Option<(u8, u8)> = None; // (rook_from, rook_to)
        let mut actual_captured_piece: Option<Piece> = None;

        // --- King Move & Castling Rights Update ---
        if moving_piece.kind == PieceType::King {
             // Determine rook movement if castling (use validated mv.is_castle)
             if mv.is_castle {
                 let (rook_from_sq, rook_to_sq) = if mv.to_sq > mv.from_sq { // Kingside
                      if moving_color == Color::White { (WHITE_KS_ROOK_START, 5) } else { (BLACK_KS_ROOK_START, 61) }
                  } else { // Queenside
                     if moving_color == Color::White { (WHITE_QS_ROOK_START, 3) } else { (BLACK_QS_ROOK_START, 59) }
                  };
                  castle_rook_move = Some((rook_from_sq, rook_to_sq));
             }
             // Update castling rights *state* for king move (Zobrist update for rights happens later).
             state.castling_rights.king_moved(moving_color);
        }

        // --- En Passant Capture Handling ---
        // Cache the EP square *before* potentially clearing it later in this function.
        let current_ep_square = state.en_passant_square;
        // Check conditions using the validated move flags and current state.
        if is_pawn_move && mv.is_capture && Some(mv.to_sq) == current_ep_square && state.get_piece_at(mv.to_sq).is_none() {
            // Calculate captured pawn square. Use wrapping arithmetic for safety, should be valid.
            let captured_pawn_sq = if moving_color == Color::White { mv.to_sq.wrapping_sub(8) } else { mv.to_sq.wrapping_add(8) };
             if captured_pawn_sq < 64 {
                 // Clear the captured pawn. `clear_square` handles the Zobrist update for the removed pawn.
                 actual_captured_piece = state.clear_square(captured_pawn_sq, &mut current_zobrist_key);
                 // Optional sanity check (log if the captured piece wasn't the opponent's pawn).
                 if actual_captured_piece.map_or(true, |p| p.kind != PieceType::Pawn || p.color == moving_color) {
                      eprintln!("WARN (apply_legal): EP capture at {} expected opponent pawn at {} but found {:?}.", index_to_algebraic(mv.to_sq), index_to_algebraic(captured_pawn_sq), actual_captured_piece);
                 }
                 // The `is_capture` flag from the input `mv` should already be true.
             } else {
                  // This should be impossible if the move was truly legal.
                  panic!("CRITICAL (apply_legal): Invalid EP capture square calculated: {}", captured_pawn_sq);
             }
        }

        // --- Move the Main Piece (Piece Movement & Zobrist Updates) ---
        // 1. Clear 'from' square. `clear_square` XORs out the moving piece's Zobrist key.
        state.clear_square(mv.from_sq, &mut current_zobrist_key);
        // 2. Clear 'to' square. If a piece is captured, `clear_square` XORs out its key and returns it.
        let captured_on_to_sq = state.clear_square(mv.to_sq, &mut current_zobrist_key);
        // Handle regular capture detection.
        if captured_on_to_sq.is_some() {
            if actual_captured_piece.is_some() {
                // Impossible state if move validation is correct.
                panic!("CRITICAL (apply_legal): Both EP capture and direct capture detected for legal move {}", mv.to_algebraic_string());
            }
            actual_captured_piece = captured_on_to_sq;
            // If a direct capture occurred but the flag was somehow false, log warning and fix.
            if !is_capture {
                eprintln!("WARN (apply_legal): Move {:?} had direct capture but is_capture flag was false.", mv);
                is_capture = true; // Correct the internal state for clock updates etc.
            }
        }
        // 3. Place the moving piece (or promoted piece) on 'to' square. `set_piece_at` XORs in the new piece's key.
        let piece_to_place_type = mv.promotion.unwrap_or(moving_piece.kind);
        state.set_piece_at(mv.to_sq, piece_to_place_type, moving_color, &mut current_zobrist_key);

        // --- Handle Castling Rook Move (Piece Movement & Zobrist Updates) ---
        if let Some((rook_from, rook_to)) = castle_rook_move {
             // Clear rook from origin. `clear_square` handles Zobrist update.
             state.clear_square(rook_from, &mut current_zobrist_key);
             // Place rook at destination. `set_piece_at` handles Zobrist update.
             state.set_piece_at(rook_to, PieceType::Rook, moving_color, &mut current_zobrist_key);
        }

        // --- Update State Variables (Castling Rights, EP, Clocks, Turn) ---

        // Update castling rights state based on rook moves/captures (if not already updated by king move).
        // Zobrist update for rights happens *after* all state changes are finalized.
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
                     WHITE_QS_ROOK_START => state.castling_rights.white_queenside = false, // Opponent's right removed
                     WHITE_KS_ROOK_START => state.castling_rights.white_kingside = false,
                     BLACK_QS_ROOK_START => state.castling_rights.black_queenside = false,
                     BLACK_KS_ROOK_START => state.castling_rights.black_kingside = false,
                     _ => {}
                 }
             }
        }

        // En Passant square update
        state.en_passant_square = None; // Reset EP target first
        if is_pawn_move {
            let rank_diff = (mv.to_sq / 8).abs_diff(mv.from_sq / 8);
            if rank_diff == 2 { // Double push creates new EP target
                let ep_target_sq = if moving_color == Color::White { mv.from_sq + 8 } else { mv.from_sq - 8 };
                state.en_passant_square = Some(ep_target_sq);
            }
        }

        // Clocks update
        // Use the potentially corrected `is_capture` status determined above.
        if is_pawn_move || is_capture {
            state.halfmove_clock = 0; // Reset clock
        } else {
            state.halfmove_clock += 1; // Increment clock
        }
        // Increment full move number after Black moves
        if moving_color == Color::Black {
            state.fullmove_number += 1;
        }

        // Switch turn to the opponent
        state.turn = moving_color.opponent();

        // --- Zobrist Key: Finalize Incremental Update ---
        // 4. XOR in keys for the *new* state components.
        current_zobrist_key ^= ZOBRIST.castling(state.castling_rights); // New castling rights
        current_zobrist_key ^= ZOBRIST.en_passant(state.en_passant_square); // New EP target (or 0)
        current_zobrist_key ^= ZOBRIST.side_to_move(state.turn); // New side to move

        // Update the board's aggregate occupancy bitboards *after* all piece movements are done.
        state.update_occupancy();

        // --- Assign the final calculated Zobrist key back to the game state ---
        self.zobrist_key = current_zobrist_key;

        // Return the piece that was actually captured (could be None)
        actual_captured_piece
    }


    // --- Public Move Execution Interface ---

    /// Attempts to make a move specified by a `Move` struct (typically parsed from user input).
    /// 1. Validates the input move against the list of currently legal moves.
    /// 2. Handles promotion prompts if necessary and applicable.
    /// 3. If legal, updates game time, applies the move using `apply_legal_move`.
    /// 4. Updates captured piece lists and Zobrist history.
    /// 5. Checks for check/checkmate after the move.
    /// 6. Records the move event.
    /// 7. Manages draw offer status (activates pending, clears opponent's active).
    /// 8. Starts the timer for the next player.
    ///
    /// # Parameters
    /// * `mv`: The `Move` struct representing the player's intended move. Note that the
    ///        `is_capture` and `is_castle` flags on this input `mv` are not strictly relied upon;
    ///        the function finds the matching *legal* move from generation, which has correct flags.
    ///        The `promotion` field *is* critical for matching pawn promotion moves.
    /// # Returns
    /// * `Ok(())` if the move was legal and successfully applied.
    /// * `Err(MoveError)` if the move was illegal for any reason (not found in legal moves,
    ///   leaves king in check, invalid pattern, etc.).
    pub fn make_legal_move(&mut self, mv: &Move) -> Result<(), MoveError> {
        // 1. Generate all legal moves for the current position.
        let legal_moves = self.generate_legal_moves(&self.current_state);

        // 2. Find the *exact* legal move that matches the user's input move.
        // Must match `from_sq`, `to_sq`, AND `promotion` type.
        let found_legal_move = legal_moves.iter().find(|&legal_mv|
            legal_mv.from_sq == mv.from_sq &&
            legal_mv.to_sq == mv.to_sq &&
            legal_mv.promotion == mv.promotion // Promotion type must match exactly!
        );

        // 3. Handle Illegal Move Attempt
        if found_legal_move.is_none() {
            // Try to provide more specific feedback about why the move failed.
            let from_piece = self.current_state.get_piece_at(mv.from_sq);

            // Check basic reasons first:
            if from_piece.is_none() {
                return Err(MoveError::PieceNotFound(mv.from_sq));
            }
            if from_piece.map_or(true, |p| p.color != self.current_state.turn) {
                return Err(MoveError::NotPlayersTurn);
            }

            // Check if the move pattern itself is fundamentally illegal or leaves king in check.
            // Simulate the move immutably to check the outcome.
             match self.apply_move_immutable_no_zobrist(&self.current_state, mv) {
                 Ok((next_state, _)) => {
                     // Check if the move, although maybe pattern-valid, leaves the king in check.
                     if self.is_in_check(&next_state, self.current_state.turn) {
                         return Err(MoveError::LeavesKingInCheck(mv.to_algebraic_string()));
                     } else {
                         // If simulation succeeds and doesn't leave king in check, but the move
                         // wasn't in `legal_moves`, it means it violated a more complex rule
                         // (like castling through check, pinned piece moving incorrectly, etc.)
                         // or the input move itself had an impossible pattern (e.g., knight e2-e5).
                         // We can differentiate slightly by checking if it was even *pseudo-legal*.
                         let pseudo_exists = self.generate_pseudo_legal_moves(&self.current_state).iter().any(|ps_mv|
                            ps_mv.from_sq == mv.from_sq && ps_mv.to_sq == mv.to_sq && ps_mv.promotion == mv.promotion
                         );
                         if pseudo_exists {
                             // The basic pattern exists but violates full legality (pin, castle path etc.)
                             return Err(MoveError::IllegalMovePattern(format!("{} (violates rules like pins or castling path/check)", mv.to_algebraic_string())));
                         } else {
                            // The basic movement pattern itself was invalid (e.g., pawn moving sideways).
                            return Err(MoveError::IllegalMovePattern(format!("{} (invalid piece movement pattern)", mv.to_algebraic_string())));
                         }
                     }
                 },
                 Err(MoveError::InternalError(e)) => {
                    // Immutable simulation failed due to internal logic error (likely inconsistent input `mv`).
                    eprintln!("Internal error check failed for {}: {}", mv.to_algebraic_string(), e);
                    return Err(MoveError::IllegalMovePattern(format!("{} (internal simulation error: {})", mv.to_algebraic_string(), e)));
                 }
                 Err(other_err) => {
                    // Propagate other specific errors from the simulation if needed.
                    return Err(other_err);
                 }
             }
        }

        // --- If move is legal ---
        let player_color = self.current_state.turn; // Record the player making the move
        // Clone the validated legal move found. This ensures we use the correct `is_capture`/`is_castle` flags.
        let legal_move_to_apply = found_legal_move.unwrap().clone();

        // 4. Activate Pending Draw Offer / Clear Active Opponent Offer
        // If the current player noted a draw offer earlier this turn...
        if self.pending_draw_offer == Some(player_color) {
            // ...make it the active offer now that they've moved.
            self.draw_offer = self.pending_draw_offer.take();
        } else {
            // Otherwise, making a move implicitly declines any active offer from the opponent.
             self.draw_offer = None;
        }
        // Always clear the pending offer flag after attempting a move.
        self.pending_draw_offer = None;

        // 5. Record Time Spent
        // Calculate time elapsed since the turn started.
        let time_spent = self.turn_start_time
            .map(|start_time| Instant::now().saturating_duration_since(start_time))
            .unwrap_or(Duration::ZERO); // Default to zero if start time wasn't recorded
        // Get mutable reference to the correct player's remaining time.
        let current_player_time_mut = match player_color {
            Color::White => &mut self.white_time_remaining,
            Color::Black => &mut self.black_time_remaining,
        };
        // Subtract the time spent (saturating_sub prevents underflow).
        *current_player_time_mut = current_player_time_mut.saturating_sub(time_spent);

        // 6. Apply the Legal Move to the main game state.
        // This updates the board, clocks, turn, EP, castling, and Zobrist key.
        let captured_piece_opt = self.apply_legal_move(&legal_move_to_apply);

         // 7. Update captured pieces list based on the result of applying the move.
         if let Some(captured) = captured_piece_opt {
              match player_color {
                  // If White moved, they captured a Black piece.
                  Color::White => self.captured_black.push(captured),
                  // If Black moved, they captured a White piece.
                  Color::Black => self.captured_white.push(captured),
              }
         }

        // 8. Update Zobrist History Count for repetition detection.
        // Increment the count for the *new* Zobrist key (representing the state *after* the move).
        let count = self.zobrist_history.entry(self.zobrist_key).or_insert(0);
        *count += 1;

        // 9. Check for Check / Checkmate *after* the move.
        // The turn has now switched, so check the status of the *new* current player (the opponent).
        let opponent_color = self.current_state.turn;
        let is_check = self.is_in_check(&self.current_state, opponent_color);
        // To check for checkmate, generate the opponent's legal moves in the *new* state.
        let opponent_legal_moves = self.generate_legal_moves(&self.current_state);
        let opponent_has_moves = !opponent_legal_moves.is_empty();
        // Checkmate is true if the opponent is in check AND has no legal moves.
        let is_checkmate = is_check && !opponent_has_moves;

        // 10. Record Move Event in the history log.
        let record = MoveRecord {
            mv_algebraic: legal_move_to_apply.to_algebraic_string(), // Use notation from the applied move
            time_taken: time_spent,
            player: player_color, // The player who just moved
            is_check,             // Is the *opponent* (now current player) in check?
            is_checkmate,         // Is the *opponent* checkmated?
        };
        self.event_history.push(GameEvent::Move(record));

        // 11. Start Timer for the next player's turn.
        self.start_turn_timer();
        Ok(()) // Indicate successful move execution
    }


    // --- Insufficient Material Logic (Enhanced) ---

     /// Checks if the current board position represents a draw due to insufficient material,
     /// according to FIDE rules (Article 5.2.2). This checks for positions where checkmate
     /// is impossible for *either* side by any sequence of legal moves.
     /// Cases covered:
     /// - King vs King (KvK)
     /// - King vs King + Knight (KvKN, KNvK)
     /// - King vs King + Bishop (KvKB, KBvK)
     /// - King + Bishop(s) vs King + Bishop(s) where *all* bishops are on squares of the same color.
     /// # Returns
     /// `true` if the material is insufficient for checkmate, `false` otherwise.
     fn is_insufficient_material(&self) -> bool {
         let state = &self.current_state;

        // Rule out positions with Pawns, Rooks, or Queens immediately.
        // If any of these pieces exist, checkmate is always theoretically possible.
        if state.wp != 0 || state.bp != 0 || state.wr != 0 || state.br != 0 || state.wq != 0 || state.bq != 0 {
            return false;
        }

        // Count remaining minor pieces (Knights and Bishops) for each side.
        let white_knights = state.wn.count_ones(); // Number of set bits = number of knights
        let black_knights = state.bn.count_ones();
        let white_bishops = state.wb.count_ones();
        let black_bishops = state.bb.count_ones();

        // Total minor pieces for each side.
        let white_minor_piece_count = white_knights + white_bishops;
        let black_minor_piece_count = black_knights + black_bishops;

        // Case 1: King vs King (bare kings)
        if white_minor_piece_count == 0 && black_minor_piece_count == 0 { return true; }

        // Case 2: King vs King + one minor piece (Knight or Bishop)
        // Check if one side has zero minors and the other has exactly one.
        if (white_minor_piece_count == 0 && black_minor_piece_count == 1) ||
           (black_minor_piece_count == 0 && white_minor_piece_count == 1) { return true; }

        // Case 3: King + Bishop(s) vs King + Bishop(s) with all bishops on the same color squares.
        // Check if both sides have *only* bishops remaining (no knights).
        if white_knights == 0 && black_knights == 0 && white_minor_piece_count > 0 && black_minor_piece_count > 0 {
            // Combine the bitboards of all bishops on the board.
            let all_bishops = state.wb | state.bb;
            // Define standard masks for dark and light squares.
            const DARK_SQUARES : u64 = 0xAA55AA55AA55AA55; // Alternating bits pattern
            const LIGHT_SQUARES: u64 = !DARK_SQUARES;      // Inverse pattern

            // Check if EITHER (all bishops are on dark squares) OR (all bishops are on light squares) is true.
            // `(all_bishops & LIGHT_SQUARES) == 0` means no bishops are on light squares (all are dark).
            // `(all_bishops & DARK_SQUARES) == 0` means no bishops are on dark squares (all are light).
            if (all_bishops & LIGHT_SQUARES == 0) || (all_bishops & DARK_SQUARES == 0) {
                return true; // Draw, as bishops on same-colored squares cannot force mate.
            }
        }

        // If none of the above specific insufficient material conditions are met,
        // assume checkmate is still possible (e.g., KBN vs K, KR vs K, etc.).
        false
    }

    /// Checks if a specific `color` has *sufficient mating material* to potentially
    /// force checkmate against a lone king opponent, assuming no opposition pieces
    /// interfere other than the king. This is primarily used for FIDE Article 6.9 (Timeout):
    /// If a player runs out of time, they lose, *unless* the opponent (the player with time remaining)
    /// *cannot possibly* checkmate the player who ran out of time (even with worst play).
    /// Sufficient material includes:
    /// - A Pawn
    /// - A Rook
    /// - A Queen
    /// - Two Knights
    /// - Two Bishops (implicitly assumes they are on different colors if count >= 2)
    /// - One Bishop and One Knight
    /// # Parameters
    /// * `color`: The color of the player whose material is being assessed.
    /// # Returns
    /// `true` if the player has sufficient material to theoretically force mate, `false` otherwise.
    fn has_sufficient_mating_material(&self, color: Color) -> bool {
        let state = &self.current_state;
        if color == Color::White {
             // A single Pawn, Rook, or Queen is always sufficient.
             if state.wp != 0 || state.wr != 0 || state.wq != 0 { return true; }
             // Two or more Knights are sufficient.
             if state.wn.count_ones() >= 2 { return true; }
             // Two or more Bishops are sufficient.
             if state.wb.count_ones() >= 2 { return true; }
             // One Bishop and one Knight are sufficient.
             if state.wn.count_ones() >= 1 && state.wb.count_ones() >= 1 { return true; }
        } else { // Check for Black
             if state.bp != 0 || state.br != 0 || state.bq != 0 { return true; }
             if state.bn.count_ones() >= 2 { return true; }
             if state.bb.count_ones() >= 2 { return true; }
             if state.bn.count_ones() >= 1 && state.bb.count_ones() >= 1 { return true; }
        }
        // Otherwise (e.g., lone King, King + Knight, King + Bishop), material is insufficient to force mate.
        false
    }


    // --- Game Termination Status Check ---

    /// Checks for automatic game termination conditions based on the current game state.
    /// This function should be called at the start of each turn *before* prompting the player.
    /// It checks for:
    /// 1. Timeout (using `has_sufficient_mating_material` for draw condition).
    /// 2. Checkmate or Stalemate (by generating legal moves for the current player).
    /// 3. Automatic draws by rule: 75-move rule, Fivefold repetition, Insufficient material.
    /// Note: Draw claims (50-move, 3-fold) and agreement/resignation are handled by player commands.
    /// # Returns
    /// * `Some(GameResult)` if the game has automatically ended based on rules.
    /// * `None` if the game is still ongoing.
    pub fn check_automatic_game_end(&self) -> Option<GameResult> {
        let state = &self.current_state;
        let current_player = state.turn;
        let opponent = current_player.opponent();

        // 1. Timeout Check (Crucial: check before move generation)
        // Check White's time
        if self.white_time_remaining == Duration::ZERO {
            // White ran out of time. Black wins UNLESS Black cannot possibly checkmate.
            return Some(if self.has_sufficient_mating_material(Color::Black) {
                // Black has mating material, Black wins.
                GameResult::Win(Color::Black, WinReason::Timeout)
            } else {
                // Black cannot mate, it's a draw.
                GameResult::Draw(DrawReason::TimeoutVsInsufficientMaterial)
            });
        }
        // Check Black's time
        if self.black_time_remaining == Duration::ZERO {
            // Black ran out of time. White wins UNLESS White cannot possibly checkmate.
            return Some(if self.has_sufficient_mating_material(Color::White) {
                // White has mating material, White wins.
                GameResult::Win(Color::White, WinReason::Timeout)
            } else {
                // White cannot mate, it's a draw.
                GameResult::Draw(DrawReason::TimeoutVsInsufficientMaterial)
            });
        }

        // 2. Checkmate / Stalemate Check
        // Generate legal moves for the player whose turn it is.
        let legal_moves = self.generate_legal_moves(state);
        // If the current player has NO legal moves:
        if legal_moves.is_empty() {
            // Check if the player is currently in check.
            return Some(if self.is_in_check(state, current_player) {
                // In check + no legal moves = Checkmate by the opponent.
                GameResult::Win(opponent, WinReason::Checkmate)
            } else {
                // Not in check + no legal moves = Stalemate.
                GameResult::Draw(DrawReason::Stalemate)
            });
        }

        // 3. Automatic Draw Rules (Check *after* Checkmate/Stalemate)
        // These rules declare a draw regardless of whose turn it is or if they have moves.

        // 75-move rule (FIDE Art. 9.6.2): If halfmove clock reaches 150 (75 full moves by each player
        // since last pawn move or capture), the game is automatically drawn.
        if state.halfmove_clock >= 150 {
            return Some(GameResult::Draw(DrawReason::SeventyFiveMoveRule));
        }
        // Fivefold repetition (FIDE Art. 9.6.1): If the same position occurs 5 times during the game
        // (tracked by Zobrist history), the game is automatically drawn.
        // Check the count for the *current* position's Zobrist key.
        if *self.zobrist_history.get(&self.zobrist_key).unwrap_or(&0) >= 5 {
            return Some(GameResult::Draw(DrawReason::FivefoldRepetition));
        }
        // Insufficient material (FIDE Art. 5.2.2): Check if checkmate is impossible.
        if self.is_insufficient_material() {
            return Some(GameResult::Draw(DrawReason::InsufficientMaterial));
        }

        // 4. No automatic end condition met
        None // Game continues
    }

    // --- Action Handlers (Draw Logic, Resign, Claim) ---

    /// Records the current player's intention to offer a draw (`pending_draw_offer`).
    /// The offer only becomes active (`draw_offer`) after the player makes their move.
    /// This prevents offering a draw without committing to a move first.
    /// # Returns
    /// * `Ok(())` if the offer was successfully noted.
    /// * `Err(CommandError)` if the player tries to offer when the opponent already has an
    ///   active offer, or if they try to offer twice in the same turn.
    pub fn offer_draw(&mut self) -> Result<(), CommandError> {
        let offering_player = self.current_state.turn;

        // Check if opponent already has an active offer waiting for response.
        if self.draw_offer == Some(offering_player.opponent()) {
             return Err(CommandError::OpponentDrawOfferPending);
        }
        // Check if this player already noted an offer this turn.
        if self.pending_draw_offer == Some(offering_player) {
             return Err(CommandError::DrawAlreadyOffered);
        }

        // Set the pending offer flag for the current player.
        self.pending_draw_offer = Some(offering_player);
        // Record the event immediately (even though offer isn't active yet).
        self.event_history.push(GameEvent::OfferDraw(offering_player));
        Ok(())
    }

    /// Accepts an *active* draw offer made by the opponent on their previous turn.
    /// Ends the game immediately as a draw by agreement.
    /// # Returns
    /// * `Ok(GameResult::Draw(DrawReason::Agreement))` if an active opponent offer was accepted.
    /// * `Err(CommandError)` if there is no active offer from the opponent, or if trying
    ///   to accept one's own (pending) offer.
    pub fn accept_draw(&mut self) -> Result<GameResult, CommandError> {
         let accepting_player = self.current_state.turn;
         // Check if `draw_offer` holds the opponent's color.
         if self.draw_offer == Some(accepting_player.opponent()) {
            println!("--- {:?} accepts the draw offer. ---", accepting_player);
            // Clear offer flags upon acceptance.
            self.draw_offer = None;
            self.pending_draw_offer = None;
            // Record the acceptance event.
            self.event_history.push(GameEvent::AcceptDraw(accepting_player));
            // Return the Draw result to signal game end.
            Ok(GameResult::Draw(DrawReason::Agreement))
        } else {
             // Provide specific error if trying to accept own offer or no offer exists.
             if self.draw_offer == Some(accepting_player) || self.pending_draw_offer == Some(accepting_player) {
                 Err(CommandError::CannotAcceptOwnDrawOffer)
             } else {
                 Err(CommandError::NoDrawToAccept)
             }
        }
    }

    /// Explicitly declines an *active* draw offer made by the opponent on their previous turn.
    /// Clears the draw offer flag, allowing the game to continue. The turn remains with
    /// the player who declined.
    /// # Returns
    /// * `Ok(())` if an active opponent offer was successfully declined.
    /// * `Err(CommandError)` if there was no active offer from the opponent, or if trying
    ///   to decline one's own (pending) offer.
    pub fn decline_draw(&mut self) -> Result<(), CommandError> {
         let declining_player = self.current_state.turn;
        // Check if `draw_offer` holds the opponent's color.
        if self.draw_offer == Some(declining_player.opponent()) {
            println!("--- {:?} declines the draw offer. ---", declining_player);
            // Clear offer flags upon decline.
            self.draw_offer = None;
            self.pending_draw_offer = None; // Also clear pending just in case.
            // Record the decline event.
            self.event_history.push(GameEvent::DeclineDraw(declining_player));
            Ok(()) // Game continues, turn remains with decliner.
         } else {
             // Provide specific error if trying to decline own offer or no offer exists.
             if self.draw_offer == Some(declining_player) || self.pending_draw_offer == Some(declining_player) {
                 Err(CommandError::CannotDeclineOwnDrawOffer)
             } else {
                 Err(CommandError::NoDrawToDecline)
             }
         }
    }

    /// The current player resigns the game. Ends the game immediately with a win for the opponent.
    /// # Returns
    /// `GameResult::Win` indicating the opponent won by resignation.
    pub fn resign(&mut self) -> GameResult {
        let resigning_player = self.current_state.turn;
        println!("--- {:?} resigns. ---", resigning_player);
        self.event_history.push(GameEvent::Resign(resigning_player));
        // Clear any outstanding draw offers on resignation.
        self.draw_offer = None;
        self.pending_draw_offer = None;
        // Return Win result for the opponent.
        GameResult::Win(resigning_player.opponent(), WinReason::Resignation)
    }

    /// Allows the current player to claim a draw based on the 50-move rule or
    /// threefold repetition rule *for the current position on the board*.
    /// Checks if the conditions for either claim are met according to FIDE rules (Art. 9.2, 9.3).
    /// If the claim is valid, ends the game as a draw.
    /// Note: FIDE rules also allow claims *before* making a move that *will* result in
    /// such a position, which is more complex and not fully implemented here (this only checks
    /// the state *after* the previous move).
    /// # Returns
    /// * `Ok(GameResult::Draw)` with the appropriate `DrawReason` if the claim is valid.
    /// * `Err(CommandError::DrawClaimInvalid)` if neither the 50-move nor 3-fold repetition
    ///   condition is met for the *current* position.
    pub fn claim_draw(&mut self) -> Result<GameResult, CommandError> {
        let claiming_player = self.current_state.turn;

        // Check 50-move rule claim (FIDE Art 9.3):
        // Player on the move can claim draw if the last 50 consecutive moves by each player
        // have been made without the movement of any pawn and without any capture.
        // This is equivalent to the halfmove clock being >= 100 (50 moves * 2 players).
        if self.current_state.halfmove_clock >= 100 {
            let reason = DrawReason::FiftyMoveRuleClaimed;
            println!("--- {:?} claims draw by 50-move rule. ---", claiming_player);
            self.event_history.push(GameEvent::ClaimDraw(claiming_player, reason));
            // Clear offers on game end.
            self.draw_offer = None; self.pending_draw_offer = None;
            return Ok(GameResult::Draw(reason));
        }

        // Check 3-fold repetition claim (FIDE Art 9.2):
        // Player on the move can claim draw if the *same position* is about to appear or
        // has just appeared for the third time.
        // We check if the *current* position's Zobrist key count is already >= 3.
        if *self.zobrist_history.get(&self.zobrist_key).unwrap_or(&0) >= 3 {
             let reason = DrawReason::ThreefoldRepetitionClaimed;
             println!("--- {:?} claims draw by threefold repetition. ---", claiming_player);
             self.event_history.push(GameEvent::ClaimDraw(claiming_player, reason));
             // Clear offers on game end.
             self.draw_offer = None; self.pending_draw_offer = None;
             return Ok(GameResult::Draw(reason));
        }

        // If neither claim condition is met for the current board state.
        Err(CommandError::DrawClaimInvalid)
    }


    // --- Stats Generation and Saving ---

    /// Generates a `GameStats` struct containing detailed statistics for the game.
    /// Processes the `event_history` to create move lists and event summaries.
    /// Includes final time remaining and the game result.
    /// # Parameters
    /// * `final_result`: An `Option<GameResult>` representing the outcome of the game.
    ///                   `None` if stats are generated before the game concluded.
    /// # Returns
    /// A `GameStats` struct populated with the game's statistics.
    fn generate_stats(&self, final_result: Option<GameResult>) -> GameStats {
        let mut white_moves_stats = Vec::new();
        let mut black_moves_stats = Vec::new();
        let mut game_events_summary = Vec::new();
        let mut total_duration = Duration::ZERO; // Accumulate duration from move times

        // Iterate through the recorded game events
        for event in &self.event_history {
            match event {
                // Process move events
                GameEvent::Move(record) => {
                    // Determine annotation based on check/checkmate status
                    let annotation = if record.is_checkmate { "#".to_string() }
                                     else if record.is_check { "+".to_string() }
                                     else { String::new() };
                    // Create a MoveStat entry
                    let move_stat = MoveStat {
                        move_algebraic: record.mv_algebraic.clone(),
                        time_taken: record.time_taken,
                        annotation,
                    };
                    // Add to the correct player's move list
                    match record.player {
                        Color::White => white_moves_stats.push(move_stat),
                        Color::Black => black_moves_stats.push(move_stat),
                    }
                    // Add move time to total duration approximation
                    total_duration += record.time_taken;
                },
                // Process non-move events into summaries
                GameEvent::OfferDraw(player) => { game_events_summary.push(GameEventSummary::OfferDraw { player: *player }); },
                GameEvent::AcceptDraw(player) => { game_events_summary.push(GameEventSummary::AcceptDraw { player: *player }); },
                GameEvent::DeclineDraw(player) => { game_events_summary.push(GameEventSummary::DeclineDraw { player: *player }); },
                GameEvent::Resign(player) => { game_events_summary.push(GameEventSummary::Resign { player: *player }); },
                GameEvent::ClaimDraw(player, reason) => { game_events_summary.push(GameEventSummary::ClaimDraw{player: *player, reason: *reason }); }
            }
        }

        // Convert the internal `GameResult` (if provided) to the serializable `GameResultReason`.
        let result_reason = final_result.map(|res| match res {
            GameResult::Win(winner, reason) => match reason {
                WinReason::Checkmate => GameResultReason::Checkmate { winner, loser: winner.opponent() },
                WinReason::Timeout => GameResultReason::Timeout { winner, loser: winner.opponent() },
                WinReason::Resignation => GameResultReason::Resignation { winner, loser: winner.opponent() },
            },
            GameResult::Draw(reason) => match reason {
                // Map internal DrawReason to serializable GameResultReason
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

        // Record final time remaining (should be non-negative due to saturating_sub).
        let white_final_time = self.white_time_remaining;
        let black_final_time = self.black_time_remaining;

        // Assemble the final GameStats struct
        GameStats {
            result: result_reason,
            white_final_time_remaining: white_final_time,
            black_final_time_remaining: black_final_time,
            total_game_duration_secs: total_duration.as_secs(),
            white_moves: white_moves_stats,
            black_moves: black_moves_stats,
            game_events: game_events_summary,
        }
    }

    /// Saves the generated game statistics to a specified file in JSON format.
    /// # Parameters
    /// * `filename`: The path to the file where statistics should be saved.
    /// * `final_result`: The final outcome of the game (`Option<GameResult>`).
    /// # Returns
    /// * `Ok(())` on successful serialization and writing to file.
    /// * `Err(SaveLoadError)` if serialization fails or an I/O error occurs during writing.
    pub fn save_stats_to_file(&self, filename: &str, final_result: Option<GameResult>) -> Result<(), SaveLoadError> {
        // Generate the statistics data for the current game state and result.
        let stats = self.generate_stats(final_result);

        // Serialize the GameStats struct to a pretty-printed JSON string.
        let json_data = serde_json::to_string_pretty(&stats)
            .map_err(SaveLoadError::Serialization)?; // Map serde error to our custom error type

        // Write the JSON string to the specified file.
        fs::write(filename, json_data)
            .map_err(|e| SaveLoadError::Io(filename.to_string(), e))?; // Map IO error

        Ok(())
    }

} // End impl Game

// --- Custom Error Types ---

/// Errors related to parsing, validating, or applying a single chess move.
#[derive(Debug)]
pub enum MoveError {
    /// Input string doesn't match expected algebraic formats (e.g., "e2e4", "a7a8q", "O-O").
    InvalidFormat(String),
    /// No piece was found on the specified 'from' square.
    PieceNotFound(u8),
    /// Attempted to move a piece belonging to the player whose turn it isn't.
    NotPlayersTurn,
    /// The attempted move would leave the player's own king in check.
    LeavesKingInCheck(String),
    /// The move follows an illegal pattern (e.g., knight moving straight) or violates
    /// specific rules like pinned piece movement, castling through check, etc.
    IllegalMovePattern(String),
    /// Invalid character used for pawn promotion (not q, r, b, or n).
    InvalidPromotion(String),
    /// An unexpected internal state or logic error occurred during move processing.
    InternalError(&'static str),
}
// Display implementation for user-friendly error messages.
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

/// Errors related to parsing or executing user commands (distinct from move errors).
#[derive(Debug)]
pub enum CommandError {
    /// The entered command word is not recognized.
    UnknownCommand(String),
    /// A required argument for a command was missing.
    MissingArgument(String),
    /// An argument provided for a command was invalid or inappropriate.
    InvalidArgument(String),
    /// An error occurred during saving or loading statistics. Wraps `SaveLoadError`.
    SaveLoadError(SaveLoadError),
    /// Player tried `offer draw` when they already have a pending offer this turn.
    DrawAlreadyOffered,
    /// Player tried `accept draw` when no active offer from the opponent exists.
    NoDrawToAccept,
    /// Player tried `decline draw` when no active offer from the opponent exists.
    NoDrawToDecline,
    /// Player tried `offer draw` when the opponent has an active offer pending response.
    OpponentDrawOfferPending,
    /// Player tried `claim draw`, but conditions (50-move, 3-fold) are not met for the current position.
    DrawClaimInvalid,
    /// Player tried to `accept draw` on their own pending or active offer.
    CannotAcceptOwnDrawOffer,
    /// Player tried to `decline draw` on their own pending or active offer.
    CannotDeclineOwnDrawOffer,
    /// A general Input/Output error occurred, likely during `stdin.read_line`.
    IoError(io::Error),
}
// Display implementation for user-friendly command error messages.
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

// Automatic conversions to simplify error handling in the main loop.
// Allows functions returning specific errors to be used where CommandError is expected.
impl From<SaveLoadError> for CommandError {
    fn from(e: SaveLoadError) -> Self { CommandError::SaveLoadError(e) }
}
impl From<io::Error> for CommandError {
    fn from(e: io::Error) -> Self { CommandError::IoError(e) }
}
impl From<MoveError> for CommandError {
    fn from(e: MoveError) -> Self {
        // Convert relevant move errors into InvalidArgument command errors.
        match e {
            MoveError::InvalidFormat(s) => CommandError::InvalidArgument(format!("Invalid move format used in command/input: {}", s)),
            MoveError::InvalidPromotion(s) => CommandError::InvalidArgument(format!("Invalid promotion used in command/input: {}", s)),
            // Other move errors (like LeavesKingInCheck, IllegalMovePattern) occurring during
            // command processing likely stem from invalid user input trying to bypass legality checks.
            _ => CommandError::InvalidArgument(format!("Invalid move input: {}", e)),
        }
    }
}

/// Errors related to saving or loading game statistics data.
#[derive(Debug)]
pub enum SaveLoadError {
    /// An error occurred during JSON serialization or deserialization. Wraps `serde_json::Error`.
    Serialization(serde_json::Error),
    /// An I/O error occurred while reading from or writing to a file. Includes filename and wraps `io::Error`.
    Io(String, io::Error),
}
// Display implementation for user-friendly save/load error messages.
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

/// Internal representation of the game's outcome, used by termination checks and action handlers.
/// Converted to `GameResultReason` for final statistics.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum GameResult {
    /// One player won for a specific reason.
    Win(Color, WinReason),
    /// The game ended in a draw for a specific reason.
    Draw(DrawReason), // Uses the shared DrawReason enum
}

/// Enumerates the reasons why a game might end with a win for one player.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize, Deserialize)]
enum WinReason { Checkmate, Timeout, Resignation }

// --- Input Parsing ---

/// Represents the different types of valid input recognized from the user.
#[derive(Debug)]
enum UserInput {
    /// A standard move attempt using algebraic notation (e.g., "e2e4", "a7a8q").
    Move(Move),
    /// A recognized text command (e.g., "offer draw", "resign", "help").
    Command(Command),
    /// A Kingside castling attempt using standard notation ("O-O" or "0-0").
    CastleKingside,
    /// A Queenside castling attempt using standard notation ("O-O-O" or "0-0-0").
    CastleQueenside,
}

/// Enumerates the recognized text commands.
#[derive(Debug)]
enum Command {
    OfferDraw, AcceptDraw, DeclineDraw,
    Resign, History, ClaimDraw, Help, Quit,
    /// Command to save statistics, includes the target filename.
    SaveStats(String),
}

/// Parses a raw user input string into a structured `UserInput` variant.
/// Distinguishes between standard moves, castling notation, and text commands.
/// Handles basic command arguments (like filename for `savestats`).
/// # Parameters
/// * `input`: The raw string entered by the user.
/// # Returns
/// * `Ok(UserInput)` if the input is recognized as a valid move format or command.
/// * `Err(CommandError)` if the input is empty, unrecognized, or has invalid arguments/format.
fn parse_user_input(input: &str) -> Result<UserInput, CommandError> {
    let trimmed_input = input.trim(); // Remove leading/trailing whitespace
    let lower_input = trimmed_input.to_lowercase(); // Use lowercase for case-insensitive matching

    // 1. Check for special Castling Notation first
    match lower_input.as_str() {
        "o-o" | "0-0" => return Ok(UserInput::CastleKingside),
        "o-o-o" | "0-0-0" => return Ok(UserInput::CastleQueenside),
        _ => {} // Not castling notation, continue parsing
    }

    // 2. Check for Text Commands
    // Split input into the first word (command) and the rest (argument)
    let mut parts = trimmed_input.splitn(2, char::is_whitespace);
    let command_word = parts.next().unwrap_or("").to_lowercase(); // First word or empty string
    let argument = parts.next().unwrap_or("").trim(); // Remainder, trimmed

    match command_word.as_str() {
        // Commands requiring specific arguments
        "offer" if argument == "draw" => return Ok(UserInput::Command(Command::OfferDraw)),
        "accept" if argument == "draw" => return Ok(UserInput::Command(Command::AcceptDraw)),
        "decline" if argument == "draw" => return Ok(UserInput::Command(Command::DeclineDraw)),
        "claim" if argument == "draw" => return Ok(UserInput::Command(Command::ClaimDraw)),
        // Single-word commands
        "resign" => return Ok(UserInput::Command(Command::Resign)),
        "history" => return Ok(UserInput::Command(Command::History)),
        "help" | "?" => return Ok(UserInput::Command(Command::Help)),
        "quit" | "exit" => return Ok(UserInput::Command(Command::Quit)),
        // Command with optional argument
        "savestats" => {
            // Use default filename if argument is empty, otherwise use the provided argument.
            let filename = if argument.is_empty() { DEFAULT_STATS_FILENAME } else { argument }.to_string();
            return Ok(UserInput::Command(Command::SaveStats(filename)));
        }
        _ => {} // Not a recognized command word, proceed to check as a move
    }

    // 3. Attempt to parse as a standard algebraic move (e.g., "e2e4", "a7a8q")
    // Use the dedicated algebraic move parser.
    parse_move_algebraic(trimmed_input)
        .map(UserInput::Move) // If successful, wrap the Move in UserInput::Move
        // If algebraic parsing fails, convert the MoveError into a CommandError
        // indicating generally invalid input.
        .map_err(|move_err| CommandError::InvalidArgument(
            format!("Unrecognized command or invalid move format: '{}' ({})", trimmed_input, move_err))
        )
}


/// Parses a string potentially representing a standard algebraic move (like "e2e4" or "a7a8q").
/// This function specifically handles the `from_sq`, `to_sq`, and optional `promotion` part.
/// It **does not** handle castling notation ("O-O", "O-O-O").
/// It **does not** validate legality, only the format. The returned `Move` struct will have
/// `is_capture` and `is_castle` initially set to `false`.
/// # Parameters
/// * `input`: The string slice potentially containing the move notation.
/// # Returns
/// * `Ok(Move)` if the string matches the expected format (4 or 5 characters, valid squares, valid promotion char if present).
/// * `Err(MoveError)` if the format is invalid (wrong length, invalid square notation, invalid promotion character).
fn parse_move_algebraic(input: &str) -> Result<Move, MoveError> {
    let trimmed = input.trim();
    // Expect 4 chars (e.g., "e2e4") or 5 chars (e.g., "a7a8q").
    if !(4..=5).contains(&trimmed.len()) {
        return Err(MoveError::InvalidFormat(trimmed.to_string()));
    }

    // Extract the 'from' and 'to' square substrings.
    let from_str = &trimmed[0..2];
    let to_str = &trimmed[2..4];

    // Convert algebraic square notation to 0-63 indices.
    let from_sq = algebraic_to_index(from_str)
                    .ok_or_else(|| MoveError::InvalidFormat(format!("Invalid 'from' square: {}", from_str)))?;
    let to_sq = algebraic_to_index(to_str)
                .ok_or_else(|| MoveError::InvalidFormat(format!("Invalid 'to' square: {}", to_str)))?;

    // Check for and parse the promotion character if the input length is 5.
    let promotion = if trimmed.len() == 5 {
        match trimmed.chars().nth(4).map(|c| c.to_ascii_lowercase()) { // Get 5th char, lowercase it
            Some('q') => Some(PieceType::Queen),
            Some('r') => Some(PieceType::Rook),
            Some('b') => Some(PieceType::Bishop),
            Some('n') => Some(PieceType::Knight),
            // Any other character is invalid for promotion.
            Some(other) => return Err(MoveError::InvalidPromotion(format!("Invalid promotion character: '{}'. Use q, r, b, or n.", other))),
            // Should be unreachable if length is 5, but handle Option defensively.
            None => return Err(MoveError::InternalError("Logic error parsing promotion char")),
        }
    } else {
        // No promotion character if length is 4.
        None
    };

    // Create the Move struct. `is_capture` and `is_castle` are initially false here.
    // Legality checks later will determine the true capture status and identify castling.
    Ok(Move { from_sq, to_sq, promotion, is_capture: false, is_castle: false })
}

// --- Helper to format Duration ---

/// Formats a `Duration` into a string like "MM:SS.mmm" (minutes, seconds, milliseconds).
/// # Parameters
/// * `duration`: The `Duration` to format.
/// # Returns
/// A `String` representing the duration.
fn format_duration(duration: Duration) -> String {
    let total_seconds = duration.as_secs();
    let minutes = total_seconds / 60;
    let seconds = total_seconds % 60;
    // Get total milliseconds and calculate the fractional part for display.
    let total_millis = duration.as_millis();
    let display_millis = total_millis % 1000;
    format!("{:02}:{:02}.{:03}", minutes, seconds, display_millis) // Pad with zeros
}

// --- Main Game Loop ---

/// The main entry point of the application.
/// Sets up the game, runs the main game loop (handling input, making moves, checking game end),
/// and handles final cleanup/stats saving.
/// # Returns
/// * `Ok(())` if the program exits normally.
/// * `Err(Box<dyn Error>)` if an unrecoverable error occurs (e.g., critical I/O failure).
fn main() -> Result<(), Box<dyn Error>> {
    println!("Starting a new game (Bitboard Version with Zobrist, Precomputation, Pins).");
    // Initialize the game state within an Option; becomes None when game quits.
    let mut game_state: Option<Game> = Some(Game::new());
    // Stores the final game result once determined.
    let mut game_result: Option<GameResult> = None;

    println!("==============================");
    println!("|   Rust Chess (Enhanced)    |");
    println!("==============================");
    print_help(); // Show commands at the start

    // Main game loop continues as long as `game_state` is Some.
    'game_loop: while let Some(game) = &mut game_state {

        // 1. Check for Automatic Game End Conditions
        // Only check if the game result hasn't already been determined (e.g., by resignation).
        if game_result.is_none() {
            game_result = game.check_automatic_game_end();
        }

        // 2. Handle Game End Sequence
        if let Some(result) = game_result {
            println!("------------------------------------------");
            println!("{}", game); // Print the final board state
            // Announce the result
            match result {
                GameResult::Win(color, reason) => println!("\n=== GAME OVER: {:?} wins by {:?}. ===", color, reason),
                GameResult::Draw(reason) => println!("\n=== GAME OVER: Draw by {:?}. ===", reason),
            }
            // Attempt to save final stats
            println!("Saving final game stats to '{}'...", DEFAULT_STATS_FILENAME);
            if let Err(e) = game.save_stats_to_file(DEFAULT_STATS_FILENAME, game_result) {
                eprintln!("Error: Failed to save final stats: {}", e);
            } else {
                println!("Stats saved successfully.");
            }
            break 'game_loop; // Exit the main game loop
        }

        // --- If Game is Ongoing ---

        // 3. Print Current State and Prompt for Input
        println!("------------------------------------------");
        println!("{}", game); // Display board, time, history, etc.

        // Prompt the correct player
        print!("\n{:?}'s turn. Enter move (e.g. e2e4, O-O) or command: ", game.current_state.turn);
        io::stdout().flush()?; // Ensure the prompt appears before reading input

        // 4. Read User Input
        let mut input_line = String::new();
        match io::stdin().read_line(&mut input_line) {
            Ok(0) => { // EOF (e.g., Ctrl+D) detected
                println!("\nEnd of input detected. Quitting game.");
                // Attempt to save stats before quitting due to EOF.
                 if let Err(e) = game.save_stats_to_file(DEFAULT_STATS_FILENAME, None) { // Pass None as result
                     eprintln!("Warning: Failed to save stats before quitting on EOF: {}", e);
                 }
                game_state = None; // Set game_state to None to terminate the loop
                continue 'game_loop; // Skip rest of the loop iteration
            }
            Ok(_) => { /* Input successfully read, proceed */ }
            Err(e) => { // Handle other read errors
                 eprintln!("Error reading input: {}. Try again or use 'quit'/'exit'.", e);
                 continue 'game_loop; // Ask for input again on the next iteration
            }
        }

        // Trim whitespace from the input line. Ignore if empty.
        let input_trimmed = input_line.trim();
        if input_trimmed.is_empty() { continue 'game_loop; }

        // 5. Parse and Process Input
        match parse_user_input(input_trimmed) {
            // --- Handle Standard Algebraic Moves ---
            Ok(UserInput::Move(mut parsed_move)) => {
                // Check if the move *looks* like a pawn promotion but lacks the promotion piece type.
                let needs_promotion_prompt = {
                    let state = &game.current_state;
                    if let Some(piece) = state.get_piece_at(parsed_move.from_sq) {
                        // Is it a pawn? Is there no promotion specified yet? Does it land on the back rank?
                        if piece.kind == PieceType::Pawn && parsed_move.promotion.is_none() {
                            let promotion_rank_mask = if piece.color == Color::White { RANK_8 } else { RANK_1 };
                            // Check if the destination square is on the promotion rank
                            (1u64 << parsed_move.to_sq) & promotion_rank_mask != 0
                        } else { false } // Not a pawn or promotion already specified
                    } else { false } // No piece at source square (should be caught by make_legal_move later anyway)
                };

                // If promotion is needed, prompt the user for the piece type.
                if needs_promotion_prompt {
                    // Before prompting, quickly check if the pawn move to that *square* is even
                    // possible (ignoring promotion type for now) to avoid unnecessary prompts.
                     let is_target_potentially_legal = game.generate_legal_moves(&game.current_state)
                         .iter()
                         .any(|m| m.from_sq == parsed_move.from_sq && m.to_sq == parsed_move.to_sq);

                    if !is_target_potentially_legal {
                        println!("Error: Moving pawn from {} to {} is not a legal destination square.",
                                 index_to_algebraic(parsed_move.from_sq), index_to_algebraic(parsed_move.to_sq));
                        continue 'game_loop; // Skip the prompt and move attempt
                    }

                    // Prompt loop for promotion choice
                    println!("Pawn promotion required for move {} to {}.", index_to_algebraic(parsed_move.from_sq), index_to_algebraic(parsed_move.to_sq));
                    loop {
                        print!("Promote pawn to? (q=Queen, r=Rook, b=Bishop, n=Knight): ");
                        io::stdout().flush()?;
                        let mut promo_input = String::new();
                        match io::stdin().read_line(&mut promo_input) {
                            Ok(0) => { // EOF during promotion prompt
                                println!("\nEnd of input during promotion. Cancelling move attempt.");
                                // Clear promotion; make_legal_move will fail without it.
                                parsed_move.promotion = None;
                                break; // Exit promotion prompt loop
                            }
                            Ok(_) => { // Input received for promotion
                                // Parse the first character (case-insensitive).
                                match promo_input.trim().to_lowercase().chars().next() {
                                    Some('q') => { parsed_move.promotion = Some(PieceType::Queen); break; },
                                    Some('r') => { parsed_move.promotion = Some(PieceType::Rook); break; },
                                    Some('b') => { parsed_move.promotion = Some(PieceType::Bishop); break; },
                                    Some('n') => { parsed_move.promotion = Some(PieceType::Knight); break; },
                                    // Invalid input, prompt again.
                                    Some(_) | None => { println!("Invalid choice. Please enter q, r, b, or n."); }
                                }
                            }
                            Err(e) => { // Error reading promotion choice
                                println!("\nError reading promotion choice: {}. Cancelling move attempt.", e);
                                parsed_move.promotion = None; // Clear promotion
                                break; // Exit promotion prompt loop
                            }
                        }
                    } // End promotion prompt loop

                     // If promotion wasn't selected (e.g., due to EOF), cancel the move attempt.
                     if parsed_move.promotion.is_none() {
                         println!("Promotion choice required but not provided. Move cancelled.");
                         continue 'game_loop;
                     }
                } // End if needs_promotion_prompt

                // Attempt to make the move (now possibly with promotion info added).
                // `make_legal_move` handles validation against legal moves.
                match game.make_legal_move(&parsed_move) {
                    Ok(()) => { /* Move was legal and applied, loop continues */ }
                    Err(e) => { println!("Error making move: {}", e); } // Print error, loop continues for retry
                }
            } // End UserInput::Move

            // --- Handle Castling Moves ---
            // Re-parse the input to determine which type of castling it was.
            Ok(UserInput::CastleKingside) | Ok(UserInput::CastleQueenside) => {
                let (king_from_sq, king_to_sq, notation) = match parse_user_input(input_trimmed).unwrap() { // Safe unwrap based on outer match
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
                    _ => unreachable!("Should only be CastleKingside or CastleQueenside here"),
                };
                // Create the castling move using the specific constructor that sets `is_castle`.
                let castle_move = Move::new_castle(king_from_sq, king_to_sq);

                // Attempt to make the castling move.
                match game.make_legal_move(&castle_move) {
                    Ok(()) => { /* Castle successful, loop continues */ }
                    Err(e) => { println!("Error making move ({}): {}", notation, e); } // Print error
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
                        // Turn does *not* pass. Loop will prompt the same player again for their move.
                    }
                    Command::AcceptDraw => {
                         match game.accept_draw() {
                             // If successful, set the game_result to end the game loop.
                             Ok(result) => { game_result = Some(result); },
                             Err(e) => println!("Error: {}", e),
                         }
                    }
                    Command::DeclineDraw => {
                         match game.decline_draw() {
                            Ok(()) => println!("Draw offer declined. It's still your turn."),
                            Err(e) => println!("Error: {}", e),
                         }
                        // Turn does *not* pass. Loop prompts same player again.
                    }
                    Command::Resign => {
                        // Resignation immediately sets the game result.
                        game_result = Some(game.resign());
                    }
                    Command::History => {
                        // Inform user that history is normally shown above the board.
                        println!("(Move history with annotations is shown above the board each turn)");
                    }
                    Command::ClaimDraw => {
                         match game.claim_draw() {
                            // If claim is valid, set game_result to end loop.
                            Ok(result) => { game_result = Some(result); },
                            Err(e) => println!("Error: {}", e),
                         }
                    }
                    Command::Help => print_help(), // Show help message
                    Command::Quit => {
                         println!("Quit command received.");
                         println!("Attempting to save game stats before quitting...");
                         // Try saving stats with None result, as game is quitting prematurely.
                         if let Err(e) = game.save_stats_to_file(DEFAULT_STATS_FILENAME, None) {
                             eprintln!("Warning: Failed to save stats before quitting: {}", e);
                         } else {
                             println!("Stats saved to {}.", DEFAULT_STATS_FILENAME);
                         }
                         println!("Exiting game.");
                         // Set game_state to None to terminate the 'while let' loop.
                         game_state = None;
                    }
                    Command::SaveStats(filename) => {
                        // Save stats with the current game result (which might be None if game is ongoing).
                        match game.save_stats_to_file(&filename, game_result) {
                            Ok(()) => { println!("Game stats saved to '{}'.", filename); }
                            Err(e) => println!("Error saving game stats: {}", e),
                        }
                    }
                } // End match command
            } // End UserInput::Command

            // --- Handle Input Parsing Errors ---
            Err(e) => {
                // Print the parsing error message (from CommandError::InvalidArgument or UnknownCommand).
                println!("Input Error: {}", e);
            }
        } // End match parse_user_input

    } // End 'game_loop: while let Some(game)

    // --- Post-Game ---
    // This section is reached only after the game loop terminates (game_state becomes None).
    println!("\nGame session finished.");
    Ok(()) // Indicate successful execution of the main function

} // End main

/// Prints a help message listing available commands and basic usage instructions.
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
