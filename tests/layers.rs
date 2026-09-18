//! Correctness of the three layers on synthetic instances: valid proofs seal,
//! invalid proofs disclose, and every malformed input discloses through the
//! check that catches it.

mod common;

use ark_bn254::{Fq, Fr};
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use common::{synthetic, twist_point_off_g2};
use grover::bits::{size_report, BinToField, Block, ProofBits};
use grover::curve::{fq_to_block, h_key, in_g2, xor, Secret, Twist, G1};
use grover::field::{FieldScheme, ProofCoords};
use grover::group::{GroupScheme, ProofPoints, KAPPA};
use grover::pgs::{Pgs, PublicMap};
use grover::{bit_scheme, Verifier};

const SID: &[u8] = b"grover/test";
const SECRET: Secret = [0x5A; 16];

fn group_scheme(vk: &Verifier) -> GroupScheme {
    GroupScheme::new(vk.clone(), SID.to_vec())
}

fn field_scheme(vk: &Verifier) -> FieldScheme {
    FieldScheme::new(vk.clone(), SID.to_vec())
}

// ------------------------------------------------------------------ groups

#[test]
fn group_layer_seals_valid_and_discloses_invalid() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = group_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);

    let enc = scheme.encode(&ek, &inst.valid);
    assert_eq!(
        scheme.eval(&program, &enc, &inst.valid),
        None,
        "valid seals"
    );

    let enc = scheme.encode(&ek, &inst.invalid);
    assert_eq!(
        scheme.eval(&program, &enc, &inst.invalid),
        Some(SECRET),
        "invalid discloses"
    );
}

/// Off the subgroup the coefficient is read from `c_t·(r·B)`.
#[test]
fn group_layer_discloses_when_b_is_off_the_subgroup() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = group_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);

    let bad = ProofPoints {
        b: twist_point_off_g2(&mut rng),
        ..inst.valid
    };
    assert!(!in_g2(&bad.b));
    let enc = scheme.encode(&ek, &bad);
    assert_eq!(
        scheme.eval(&program, &enc, &bad),
        Some(SECRET),
        "step 1 opens s"
    );
}

#[test]
fn group_layer_accepts_the_point_at_infinity() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = group_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);

    // Each proof point at infinity in turn. B = O lies in G_2 (r·O = O), so it
    // reaches the commitments; all three make the proof invalid.
    let cases = [
        ProofPoints {
            a: G1::zero(),
            ..inst.valid
        },
        ProofPoints {
            b: Twist::zero(),
            ..inst.valid
        },
        ProofPoints {
            c: G1::zero(),
            ..inst.valid
        },
    ];
    for x in cases {
        assert!(!inst.vk.is_valid(&x));
        let enc = scheme.encode(&ek, &x);
        assert_eq!(scheme.eval(&program, &enc, &x), Some(SECRET));
    }
}

#[test]
fn group_layer_ignores_a_tampered_program() {
    // A wrong commitment on one component makes the search fail to decode uniquely.
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = group_scheme(&inst.vk);
    let (mut program, ek) = scheme.garble(&mut rng, &SECRET);
    program.commits[3] = [0u8; 32];
    let enc = scheme.encode(&ek, &inst.invalid);
    assert_eq!(scheme.eval(&program, &enc, &inst.invalid), None);
}

/// A label on `B` outside `G_2` is rejected rather than fed to the pairing.
#[test]
fn group_layer_rejects_a_label_outside_g2() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = group_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);
    let mut enc = scheme.encode(&ek, &inst.invalid);
    enc.b[0] += twist_point_off_g2(&mut rng);
    assert_eq!(scheme.eval(&program, &enc, &inst.invalid), None);
}

/// Encoding information must be used once. Two encodings under the same keys,
/// for two different values of `B`, subtract to `c_t·(B' − B)`, and enumerating
/// `{0, 1}` recovers every `c_t` and hence the pad on `s`. Both proofs can be
/// valid: for `a ∈ F_r^×`, `(aA, a^{-1}B, C)` preserves the pairing equation.
///
/// This is a condition on the surrounding protocol, not something the scheme can
/// enforce, so the test records the attack rather than a defence.
#[test]
fn reusing_encoding_information_recovers_the_secret() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = group_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);

    let a = Fr::from(7u64);
    let other = ProofPoints {
        a: inst.valid.a * a,
        b: inst.valid.b * a.inverse().unwrap(),
        c: inst.valid.c,
    };
    assert!(inst.vk.is_valid(&other) && inst.vk.is_valid(&inst.valid));

    let first = scheme.encode(&ek, &inst.valid);
    let second = scheme.encode(&ek, &other);
    assert_eq!(
        scheme.eval(&program, &first, &inst.valid),
        None,
        "one use seals"
    );

    let delta = other.b - inst.valid.b;
    let recovered: Vec<bool> = (0..KAPPA)
        .map(|t| {
            let d = second.b[t] - first.b[t];
            if d.is_zero() {
                false
            } else {
                assert_eq!(d, delta);
                true
            }
        })
        .collect();
    let bytes: Vec<u8> = recovered.iter().map(|&c| c as u8).collect();
    let opened = xor(&program.ct, &h_key(SID, &bytes));
    assert_eq!(
        opened, SECRET,
        "two encodings open the secret on a valid proof"
    );
}

// ------------------------------------------------------------------ fields

#[test]
fn field_layer_seals_valid_and_discloses_invalid() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = field_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);

    let valid = ProofCoords::from_points(&inst.valid).unwrap();
    let enc = scheme.encode(&ek, &valid);
    assert_eq!(scheme.eval(&program, &enc, &valid), None);

    let invalid = ProofCoords::from_points(&inst.invalid).unwrap();
    let enc = scheme.encode(&ek, &invalid);
    assert_eq!(scheme.eval(&program, &enc, &invalid), Some(SECRET));
}

#[test]
fn field_layer_discloses_off_curve_coordinates() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = field_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);
    let valid = ProofCoords::from_points(&inst.valid).unwrap();

    // A off the curve.
    let mut x = valid;
    x.a.1 += Fq::one();
    assert!(x.to_points().is_none());
    let enc = scheme.encode(&ek, &x);
    assert_eq!(
        scheme.eval(&program, &enc, &x),
        Some(SECRET),
        "check on A opens s"
    );

    // B off the twist.
    let mut x = valid;
    x.b.0.c1 += Fq::one();
    assert!(x.to_points().is_none());
    let enc = scheme.encode(&ek, &x);
    assert_eq!(
        scheme.eval(&program, &enc, &x),
        Some(SECRET),
        "check on B opens s"
    );

    // C off the curve.
    let mut x = valid;
    x.c.0 += Fq::one();
    let enc = scheme.encode(&ek, &x);
    assert_eq!(
        scheme.eval(&program, &enc, &x),
        Some(SECRET),
        "check on C opens s"
    );
}

#[test]
fn field_layer_discloses_the_zero_secret_off_curve() {
    // With s = 0 the check polynomials are identically zero; the evaluator must
    // still output s (= 0), not ⊥, because it branches on the public curve equation.
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = field_scheme(&inst.vk);
    let zero: Secret = [0u8; 16];
    let (program, ek) = scheme.garble(&mut rng, &zero);
    let mut x = ProofCoords::from_points(&inst.valid).unwrap();
    x.a.1 += Fq::one();
    let enc = scheme.encode(&ek, &x);
    assert_eq!(scheme.eval(&program, &enc, &x), Some(zero));
}

#[test]
fn field_layer_discloses_b_off_the_subgroup() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = field_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);

    let bad = ProofPoints {
        b: twist_point_off_g2(&mut rng),
        ..inst.valid
    };
    let x = ProofCoords::from_points(&bad).unwrap();
    let enc = scheme.encode(&ek, &x);
    assert_eq!(scheme.eval(&program, &enc, &x), Some(SECRET));
}

/// A proof chosen after the masks are known still discloses.
///
/// The party that generates the garbling also supplies the proof, so it can aim
/// an input straight at the coordinate encoder's degenerate case: pick `A` with
/// `b_i·A = M_i` for an entry whose coefficient is `1`. The incomplete addition
/// law then returns the all-zero triple at that entry, which the decoder handles
/// exactly. Without the repair this case returned `⊥`.
#[test]
fn field_layer_discloses_on_a_proof_aimed_at_the_masks() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = field_scheme(&inst.vk);
    let (program, ek_f, ek_g) = scheme.garble_parts(&mut rng, &SECRET);

    // The first entry on A whose coefficient is one.
    let i = ek_g
        .a_coeffs
        .iter()
        .position(|&c| c)
        .expect("−k has a set bit");
    let a = ek_g.a_keys[i];

    let aimed = ProofPoints { a, ..inst.valid };
    assert!(!inst.vk.is_valid(&aimed), "the aimed proof is invalid");
    let x = ProofCoords::from_points(&aimed).unwrap();
    let enc = scheme.encode(&ek_f, &x);
    assert_eq!(
        scheme.eval(&program, &enc, &x),
        Some(SECRET),
        "a proof aimed at mask {i} must still disclose"
    );
}

// -------------------------------------------------------------------- bits

#[test]
fn bit_layer_end_to_end() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = bit_scheme(inst.vk.clone(), SID.to_vec());
    let (program, ek) = scheme.garble(&mut rng, &SECRET);

    let report = size_report(&program);
    eprintln!(
        "group {} KiB, dfb ciphertexts {} KiB, dfb output decoding {} KiB, total {:.3} MiB",
        report.group_bits / 8192,
        report.dfb_ciphertext_bits / 8192,
        report.dfb_output_decoding_bits / 8192,
        report.total_bits() as f64 / (8.0 * 1024.0 * 1024.0)
    );

    let valid = ProofBits::from_coords(&ProofCoords::from_points(&inst.valid).unwrap());
    let enc = scheme.encode(&ek, &valid);
    assert_eq!(
        scheme.eval(&program, &enc, &valid),
        None,
        "valid proof seals"
    );

    let invalid = ProofBits::from_coords(&ProofCoords::from_points(&inst.invalid).unwrap());
    let enc = scheme.encode(&ek, &invalid);
    assert_eq!(
        scheme.eval(&program, &enc, &invalid),
        Some(SECRET),
        "invalid proof discloses"
    );
}

#[test]
fn bit_layer_reduces_non_canonical_blocks() {
    // A block holding coordinate + p describes the same valid proof: ι_bin reduces
    // it, so the output is ⊥, unlike the deployed verifier which rejects it.
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = bit_scheme(inst.vk.clone(), SID.to_vec());
    let (program, ek) = scheme.garble(&mut rng, &SECRET);

    let coords = ProofCoords::from_points(&inst.valid).unwrap();
    let mut x = ProofBits::from_coords(&coords);
    let mut big = coords.a.0.into_bigint();
    let carry = big.add_with_carry(&Fq::MODULUS);
    assert!(!carry);
    let bytes = big.to_bytes_le();
    x.blocks[Block::AU as usize].copy_from_slice(&bytes[..32]);
    assert_ne!(x.blocks[Block::AU as usize], fq_to_block(coords.a.0));
    assert_eq!(BinToField.apply(&x), coords);

    let enc = scheme.encode(&ek, &x);
    assert_eq!(scheme.eval(&program, &enc, &x), None);
}

#[test]
fn bit_layer_discloses_malformed_inputs() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = bit_scheme(inst.vk.clone(), SID.to_vec());
    let (program, ek) = scheme.garble(&mut rng, &SECRET);
    let coords = ProofCoords::from_points(&inst.valid).unwrap();

    // Off-curve A, given as bits.
    let mut off = coords;
    off.a.0 += Fq::one();
    let x = ProofBits::from_coords(&off);
    let enc = scheme.encode(&ek, &x);
    assert_eq!(scheme.eval(&program, &enc, &x), Some(SECRET), "off-curve A");

    // Off-curve B, given as bits.
    let mut off = coords;
    off.b.1.c0 += Fq::one();
    let x = ProofBits::from_coords(&off);
    let enc = scheme.encode(&ek, &x);
    assert_eq!(scheme.eval(&program, &enc, &x), Some(SECRET), "off-twist B");

    // B on the twist but off G_2, given as bits.
    let bad = ProofPoints {
        b: twist_point_off_g2(&mut rng),
        ..inst.valid
    };
    let x = ProofBits::from_coords(&ProofCoords::from_points(&bad).unwrap());
    let enc = scheme.encode(&ek, &x);
    assert_eq!(
        scheme.eval(&program, &enc, &x),
        Some(SECRET),
        "B off the subgroup"
    );
}

// -------------------------------------------------------------- exact sizes

/// The exact bit counts of a garbled program.
///
/// Measured against the `duty-free-bits` commit pinned in `Cargo.toml`.
#[test]
fn exact_program_size() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = bit_scheme(inst.vk, SID.to_vec());
    let (program, _) = scheme.garble(&mut rng, &SECRET);
    let report = size_report(&program);

    // group_bits: kappa compressed G_2 elements (64 bytes each, arkworks'
    // actual serializer, not a hard-coded per-point width) + kappa 32-byte
    // commitments + one 16-byte secret.
    assert_eq!(report.group_bits, 128 * 512 + 128 * 256 + 128);
    assert_eq!(report.group_bits, 98_432);

    // The Duty-Free Bits accounting is deterministic given the fixed CRT
    // parameters and entry counts: it does not depend on the random proof or
    // secret, only on the fixed widths
    assert_eq!(report.dfb_ciphertext_bits, 13_821_010);
    assert_eq!(report.dfb_output_decoding_bits, 6_573_138);

    assert_eq!(report.total_bits(), 20_492_580);
    let mib = report.total_bits() as f64 / (8.0 * 1024.0 * 1024.0);
    assert!((mib - 2.4429).abs() < 1e-3, "total {mib:.4} MiB");
}

/// `bits::N_BASE`, derived from `group::N` and `group::KAPPA`, and
/// `FieldLayout::base_field_entries()`, derived independently from the
/// per-point coordinate layout, must agree
#[test]
fn n_base_matches_field_layout() {
    use grover::bits::N_BASE;
    use grover::field::FieldLayout;
    assert_eq!(N_BASE, FieldLayout::new().base_field_entries());
    assert_eq!(N_BASE, 10_758);
}

// ---------------------------------------------------- defensive length checks

/// A truncated group program must not panic the evaluator: the party
/// publishing it is the one that wants disclosure not to happen.
#[test]
fn group_layer_rejects_a_truncated_program() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = group_scheme(&inst.vk);
    let (mut program, ek) = scheme.garble(&mut rng, &SECRET);
    program.bases.pop();
    program.commits.pop();
    let enc = scheme.encode(&ek, &inst.invalid);
    assert_eq!(scheme.eval(&program, &enc, &inst.invalid), None);
}

/// The same, at the bit layer: a program or encoding with fewer than the
/// expected eight per-block instances must disclose nothing rather than
/// panic. `BitEncoder::eval`'s `Pgs::Output` is not `Option`-shaped, so it
/// degrades to an empty `FieldEncoding`, which `FieldScheme::eval`'s existing
/// length guard then rejects.
#[test]
fn bit_layer_rejects_a_truncated_program() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = bit_scheme(inst.vk.clone(), SID.to_vec());
    let (mut program, ek) = scheme.garble(&mut rng, &SECRET);
    program.1.instances.pop();
    let invalid = ProofBits::from_coords(&ProofCoords::from_points(&inst.invalid).unwrap());
    let enc = scheme.encode(&ek, &invalid);
    assert_eq!(scheme.eval(&program, &enc, &invalid), None);
}

/// A proof aimed at one of `B`'s own masks, mirroring the `A`-side regression
/// test above, closing the same gap for the twist.
#[test]
fn field_layer_discloses_on_a_proof_aimed_at_bs_mask() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = field_scheme(&inst.vk);
    let (program, ek_f, ek_g) = scheme.garble_parts(&mut rng, &SECRET);

    let t = ek_g
        .coeffs
        .iter()
        .position(|&c| c)
        .expect("c⃗ has a set bit");
    let aimed = ProofPoints {
        b: ek_g.b_keys[t],
        ..inst.valid
    };
    assert!(!inst.vk.is_valid(&aimed), "the aimed proof is invalid");
    let x = ProofCoords::from_points(&aimed).unwrap();
    let enc = scheme.encode(&ek_f, &x);
    assert_eq!(
        scheme.eval(&program, &enc, &x),
        Some(SECRET),
        "a proof aimed at B's mask {t} must still disclose"
    );
}

// ------------------------------------------------------------------- timing

/// Wall-clock time for `Garb`, `Enc`, and `Eval`, on this machine.
///
/// Reports the minimum over several runs (garbling and evaluation have no
/// data-dependent branching that would make the minimum unrepresentative,
/// so it is the appropriate summary for removing scheduling noise, not an
/// average). `Eval` is timed separately for a valid and an invalid proof:
/// `GroupScheme::eval` returns as soon as it sees `P = 0`, before running the
/// per-entry commitment search.
#[test]
#[ignore]
fn timing() {
    use std::time::{Duration, Instant};

    const RUNS: usize = 10;
    fn min_of(mut f: impl FnMut() -> Duration) -> Duration {
        (0..RUNS).map(|_| f()).min().unwrap()
    }

    let mut rng = ark_std::test_rng();
    let inst = synthetic(&mut rng);
    let scheme = bit_scheme(inst.vk.clone(), SID.to_vec());
    let valid = ProofBits::from_coords(&ProofCoords::from_points(&inst.valid).unwrap());
    let invalid = ProofBits::from_coords(&ProofCoords::from_points(&inst.invalid).unwrap());

    let garble_time = min_of(|| {
        let start = Instant::now();
        let _ = scheme.garble(&mut rng, &SECRET);
        start.elapsed()
    });

    let (program, ek) = scheme.garble(&mut rng, &SECRET);

    let encode_time = min_of(|| {
        let start = Instant::now();
        let _ = scheme.encode(&ek, &valid);
        start.elapsed()
    });

    let enc_valid = scheme.encode(&ek, &valid);
    let enc_invalid = scheme.encode(&ek, &invalid);

    let eval_valid_time = min_of(|| {
        let start = Instant::now();
        let out = scheme.eval(&program, &enc_valid, &valid);
        assert_eq!(out, None);
        start.elapsed()
    });
    let eval_invalid_time = min_of(|| {
        let start = Instant::now();
        let out = scheme.eval(&program, &enc_invalid, &invalid);
        assert_eq!(out, Some(SECRET));
        start.elapsed()
    });

    eprintln!("Garb:            {garble_time:?}");
    eprintln!("Enc:             {encode_time:?}");
    eprintln!("Eval (valid):    {eval_valid_time:?}");
    eprintln!("Eval (invalid):  {eval_invalid_time:?}");
    eprintln!(
        "Garb + Enc + Eval (invalid), single-shot total: {:?}",
        garble_time + encode_time + eval_invalid_time
    );
}
