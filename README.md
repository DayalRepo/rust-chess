# Rust Chess Engine

A feature-rich chess engine implemented in Rust, using efficient bitboard representation.

## Features

- Complete chess rules implementation including:
  - Castling (kingside and queenside)
  - En passant captures
  - Pawn promotion
  - Check and checkmate detection
  - Stalemate detection
- Draw conditions:
  - Insufficient material
  - 50/75 move rule
  - 3/5-fold repetition
  - Draw by agreement
- Game management:
  - Time controls (15 minute default)
  - Move history tracking
  - Game statistics
  - Draw offers and claims
- Efficiency:
  - Bitboard representation for fast move generation
  - Zobrist hashing for position tracking
  - Pre-computed attack tables

## Usage

Build and run the project with Cargo:

```
cargo build --release
cargo run --release
```

### Commands

While playing:
- Move using algebraic notation (e.g., `e2e4`, `g1f3`)
- Castle using `O-O` (kingside) or `O-O-O` (queenside)
- `/offer-draw` - Offer a draw to opponent
- `/accept-draw` - Accept opponent's draw offer
- `/decline-draw` - Decline opponent's draw offer
- `/claim-draw` - Claim a draw (50-move rule or 3-fold repetition)
- `/resign` - Resign the game
- `/history` - Show game move history
- `/help` - Display available commands
- `/quit` - Exit the program

## Implementation Details

The chess engine uses bitboards for efficient board representation and move generation. Each piece type for each color has its own 64-bit integer where set bits represent piece locations. This approach allows for fast move generation using bitwise operations.

The engine implements Zobrist hashing for position tracking to detect draws by repetition. It also includes comprehensive validation for all chess rules including pin detection, check evasion, and legal move filtering.

## License

This project is open source and available under the MIT License. 