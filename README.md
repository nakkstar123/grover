# grover

Rust implementation of the garbled Groth16 verifier described in the paper.
Binary coefficients only (no complex multiplication).

## Build

```
cargo build
```

Pulls `duty-free-bits` from GitHub at a pinned commit (see `Cargo.toml`).

## Test

```
cargo test --release
```

32 tests: 12 unit, 1 against a real `ark-groth16` proof, 19 integration
tests covering each layer, malformed inputs, and the exact garbled program
size.

A timing benchmark is included but ignored by default:

```
cargo test --release --test layers timing -- --nocapture --ignored
```

## Layout

- `src/curve.rs` — BN254 and hashing.
- `src/itpg.rs`, `src/pointenc.rs` — polynomial garbling and the coordinate
  encoder built from it.
- `src/group.rs`, `src/field.rs`, `src/bits.rs` — the three layers of the
  construction, over group elements, field coordinates, and bit strings.
- `src/pgs.rs` — the shared interface between layers.
