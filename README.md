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

63 tests: 15 unit, 3 against real `ark-groth16` proofs, 4 against a proof in
SP1's wire format, 41 integration tests covering each layer, malformed inputs,
and the exact garbled program size.

A timing benchmark is included but ignored by default:

```
cargo test --release --test layers timing -- --nocapture --ignored
```

## Statement inputs

A statement scalar `ξ_i` is either folded into `D` at garbling time or left to the
evaluator as part of the proof. A verifier for an SP1 program can fold every public
input except the digest of the public values, which differs per deposit, so leaving
it to the evaluator lets one garbling serve many deposits. List the bases of the
scalars left to the evaluator in `Verifier::input_bases`, and put their values in
`ProofPoints::inputs`. With none, the scheme is exactly the fixed-statement one.

The garbler adds `κ` labels `z_{i,t} = c_t·ξ_i + ρ_{i,t}`, and the evaluator forms
`Σ_i z_{i,t}·vk_i`. At the bit layer each scalar is one more 256-bit block and one
more Duty-Free Bits instance, over `F_r`, at 1,062,400 bits (130 KiB) of program:
2.443 MiB with no scalars, 2.570 MiB with one. `f~_G` does not grow. `bit_scheme`
accepts up to `MAX_INPUTS = 43`, past which the 40-bit aggregate target fails.

The scheme does not enforce three conditions on the surrounding protocol:

- **One label per bit, per garbling.** Labels for two values of `ξ_i` subtract to
  `c_t·(ξ'_i − ξ_i)` and open `s`, with no proof involved; the test
  `reusing_statement_labels_recovers_the_secret` records this. Two different blocks
  are enough even if they reduce to the same `ξ_i`, as `ξ_i` and `ξ_i + r` do: both
  labels of one bit reveal that instance's offset, and with it the labels of every
  other block.
- **The garbler must not choose the statement.** The function decides the proof
  against the `ξ_i` it is given, so a valid proof of another statement seals. Where
  the party releasing labels gains from sealing, as a watchtower does in a dispute,
  it can seal against an honest evaluator by proving the wrong statement. The
  protocol must commit to the bits of `ξ_i` so that only the expected value can be
  released, and for SP1 fix that value as the hash of the expected public values,
  which this crate does not compute.
- **Selective security.** Privacy is argued with the whole input, proof and
  statement, fixed before the program is published. The transformation that lifts
  this, encrypting the program under a key released with the labels, is not
  implemented here.

## Layout

- `src/curve.rs` — BN254 and hashing.
- `src/itpg.rs`, `src/pointenc.rs` — polynomial garbling and the coordinate
  encoder built from it.
- `src/group.rs`, `src/field.rs`, `src/bits.rs` — the three layers of the
  construction, over group elements, field coordinates, and bit strings.
- `src/pgs.rs` — the shared interface between layers.
