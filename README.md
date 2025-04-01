# Rust Chess Engine

A high-performance chess engine implemented in Rust with a focus on efficient bitboard representation, comprehensive rule implementation, and robust game management.

## Table of Contents
- [Features](#features)
- [Technical Architecture](#technical-architecture)
- [Installation](#installation)
- [Usage](#usage)
- [Game Commands](#game-commands)
- [Implementation Details](#implementation-details)
  - [Bitboard Representation](#bitboard-representation)
  - [Move Generation](#move-generation)
  - [Checking for Check](#checking-for-check)
  - [Legal Move Filtering](#legal-move-filtering)
  - [Zobrist Hashing](#zobrist-hashing)
  - [Time Management](#time-management)
  - [Game State Tracking](#game-state-tracking)
- [Draw Conditions](#draw-conditions)
- [Statistics and Game Analysis](#statistics-and-game-analysis)
- [Performance Considerations](#performance-considerations)
- [Dependencies](#dependencies)
- [License](#license)

## Features

### Core Chess Rules
- Complete chess rules implementation with efficient bitboard representation
- Algebraic notation support (e.g., `e2e4`, `a7a8q`)
- Castling (kingside `O-O` and queenside `O-O-O`)
- En passant captures
- Pawn promotion to any legal piece
- Detection of all special positions:
  - Check and checkmate detection
  - Stalemate detection
  - Pin detection and handling
  - Legal move filtering based on king safety

### Advanced Game Management
- Comprehensive draw conditions:
  - 50-move rule (claimable) and 75-move rule (automatic)
  - 3-fold repetition (claimable) and 5-fold repetition (automatic)
  - Insufficient material detection
  - Draw by agreement
- Time controls with 15-minute default per player
- Move history tracking with check/checkmate annotations
- Game statistics collection and JSON export
- Draw offers, acceptances, claims and declines
- Resignation handling

### Technical Features
- Zobrist hashing for efficient position tracking and repetition detection
- Pre-computed attack tables for fast move generation
- Efficient bitboard operations for move validation
- Detailed error handling with custom error types
- Game state serialization for analysis

## Technical Architecture

The engine uses a bitboard-based architecture where each piece type for each color is represented by a 64-bit integer. This provides extremely fast move generation and position evaluation through bitwise operations.

### Key Components:

1. **BitboardState**: Core representation of the chess position
   - Individual bitboards for each piece type and color
   - Combined occupancy bitboards for fast collision detection
   - Game state tracking (castling rights, en passant, etc.)

2. **Game**: High-level game management
   - Move application and validation
   - Time control
   - Game termination conditions
   - Draw handling
   - Game history and statistics

3. **ZobristTable**: Position hashing for repetition detection
   - Unique hash keys for each piece/square combination
   - Hash components for castling rights, en passant, and side to move

4. **Move Generation**: Specialized for each piece type
   - Knight/King: Pre-computed attack tables
   - Sliding pieces: Ray-based move generation
   - Pawns: Specialized move and capture generation with promotion handling

## Installation

### Prerequisites
- Rust and Cargo (latest stable version recommended)

### Build from Source
```bash
# Clone the repository
git clone https://github.com/DayalRepo/rust-chess.git
cd rust-chess

# Build in release mode for best performance
cargo build --release

# Run the chess engine
cargo run --release
```

## Usage

The chess engine runs as a console application with an interactive interface:

```
------------------------------------------
  a b c d e f g h
8 r n b q k b n r 8
7 p p p p p p p p 7
6 . . . . . . . . 6
5 . . . . . . . . 5
4 . . . . . . . . 4
3 . . . . . . . . 3
2 P P P P P P P P 2
1 R N B Q K B N R 1
  a b c d e f g h

White's turn. Enter move (e.g. e2e4, O-O) or command:
```

Players take turns entering moves in algebraic notation. The board is displayed after each move, along with time remaining and move history.

## Game Commands

During gameplay, the following commands are available:

- **Move Entry**: Enter moves in algebraic notation (e.g., `e2e4`, `a7a8q`)
- **Castling**: Use `O-O` for kingside castle or `O-O-O` for queenside castle
- **Draw Handling**:
  - `/offer-draw` - Offer a draw to opponent
  - `/accept-draw` - Accept opponent's draw offer
  - `/decline-draw` - Decline opponent's draw offer
  - `/claim-draw` - Claim a draw by 50-move rule or 3-fold repetition
- **Game Management**:
  - `/resign` - Resign the game
  - `/history` - Show game move history
  - `/savestats [filename]` - Save game statistics to a file
  - `/help` - Display available commands
  - `/quit` or `/exit` - Exit the program

## Implementation Details

### Bitboard Representation

The engine uses a 64-bit integer (u64) for each piece type and color, where set bits represent piece locations:

```rust
struct BitboardState {
    wp: u64, wn: u64, wb: u64, wr: u64, wq: u64, wk: u64, // White pieces
    bp: u64, bn: u64, bb: u64, br: u64, bq: u64, bk: u64, // Black pieces
    white_occupied: u64,
    black_occupied: u64,
    occupied: u64,
    // Additional state information...
}
```

Bitboards enable extremely fast move generation through bitwise operations. For example, to find all knight moves from a square:

```rust
// Pre-computed attack table lookup
let knight_moves = KNIGHT_ATTACKS[square] & !friendly_pieces;
```

### Move Generation

The engine uses specialized move generation for each piece type:

1. **Pre-computed Tables**: Knights and kings use lookup tables for all possible moves from any square
2. **Sliding Piece Algorithm**: Rooks, bishops, and queens use efficient ray-casting with bitboard operations
3. **Pawn Move Generation**: Special handling for pawn moves, double pushes, captures, and promotions

### Checking for Check

Check detection uses attack pattern generation from the king's position:

```rust
// Is square attacked by any opponent piece?
fn is_square_attacked(&self, square: u8, by_color: Color) -> bool {
    let sq_bb = 1u64 << square;
    // Check attacks from each piece type...
}

// Is the king of the given color in check?
fn is_in_check(&self, color: Color) -> bool {
    let king_sq = self.find_king(color);
    self.is_square_attacked(king_sq, color.opponent())
}
```

### Legal Move Filtering

All moves are first generated as pseudo-legal moves, then filtered to remove those that would leave the king in check:

1. Generate all pseudo-legal moves based on piece movement patterns
2. Apply each move on a temporary board copy
3. Check if the resulting position leaves the king in check
4. Discard illegal moves

### Zobrist Hashing

Position hashing for repetition detection:

```rust
struct ZobristTable {
    piece_keys: [[[u64; 64]; 6]; 2],
    castling_keys: [[[[u64; 2]; 2]; 2]; 2],
    en_passant_keys: [u64; 64],
    black_to_move_key: u64,
}
```

Each position gets a unique hash by XORing together keys for:
- Each piece on each square
- Current castling rights
- En passant target square (if any)
- Side to move

### Time Management

The engine includes a time control system:

```rust
// Default time control: 15 minutes per player
const INITIAL_TIME_SECONDS: u64 = 15 * 60;

// Time tracking in Game struct
struct Game {
    white_time_remaining: Duration,
    black_time_remaining: Duration,
    move_start_time: Option<Instant>,
    // ...
}
```

Time is tracked per player and updated after each move. The game can end on time forfeit.

### Game State Tracking

The engine maintains comprehensive game state:

```rust
struct Game {
    // Current position state
    current_state: BitboardState,
    
    // History tracking
    move_history: Vec<MoveRecord>,
    event_history: Vec<GameEvent>,
    zobrist_history: HashMap<u64, u8>, // Position -> count for repetition detection
    zobrist_key: u64,                  // Current position hash
    
    // Draw handling
    draw_offer: Option<Color>,         // Active offer
    pending_draw_offer: Option<Color>, // Offer made this turn
    
    // Time control
    white_time_remaining: Duration,
    black_time_remaining: Duration,
    move_start_time: Option<Instant>,
}
```

## Draw Conditions

The engine implements all standard draw conditions:

1. **Stalemate**: No legal moves but not in check
2. **Insufficient Material**: Automatically detects endgames where checkmate is impossible:
   - King vs. King
   - King + Bishop/Knight vs. King
   - King + Bishop vs. King + Bishop (same color bishops)
3. **Repetition**:
   - Three-fold repetition (claimable by player)
   - Five-fold repetition (automatic draw)
4. **Move Rule**:
   - 50-move rule (claimable by player)
   - 75-move rule (automatic draw)
5. **Draw by Agreement**: Offer and acceptance handling

## Statistics and Game Analysis

After each game, statistics are saved to a JSON file:

```json
{
  "result": { "type": "Checkmate", "winner": "White", "loser": "Black" },
  "white_final_time_remaining": 840.5,
  "black_final_time_remaining": 723.2,
  "total_game_duration_secs": 336,
  "white_moves": [
    { "move_algebraic": "e2e4", "time_taken": 4.2, "annotation": "" },
    // ...
  ],
  "black_moves": [
    { "move_algebraic": "e7e5", "time_taken": 3.8, "annotation": "" },
    // ...
  ],
  "game_events": [
    { "type": "OfferDraw", "player": "White" },
    { "type": "DeclineDraw", "player": "Black" }
  ]
}
```

## Performance Considerations

The engine is optimized for performance:

1. **Bitboard Operations**: Fast bitwise operations for move generation and validation
2. **Pre-computed Tables**: Lookup tables for common calculations
3. **Zobrist Incremental Updates**: Hash keys are updated incrementally rather than recalculated
4. **Move Legality Filtering**: Early pruning of impossible moves
5. **Immutable Position Updates**: Copy-on-write semantics for move application

## Dependencies

The Rust Chess Engine relies on the following crates:

- **serde** and **serde_json** (1.0): For game state serialization to JSON
- **rand** (0.9.0): For generating Zobrist hash keys
- **lazy_static** (1.4): For precomputed lookup tables
- **regex** (1.5): For input parsing and validation

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
