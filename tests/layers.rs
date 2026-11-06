//! Correctness of the three layers on synthetic instances: valid proofs seal,
//! invalid proofs disclose, and every malformed input discloses through the
//! check that catches it.

mod common;

use ark_bn254::{Fq, Fr};
use ark_ff::{BigInteger, Field, One, PrimeField, UniformRand, Zero};
use common::{synthetic, synthetic_with_inputs, twist_point_off_g2};
use grover::bits::{n_base, size_report, BinToField, Block, ProofBits};
use grover::curve::{fq_to_block, fr_to_block, h_key, in_g2, xor, Secret, Twist, G1};
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
        ..inst.valid.clone()
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
            ..inst.valid.clone()
        },
        ProofPoints {
            b: Twist::zero(),
            ..inst.valid.clone()
        },
        ProofPoints {
            c: G1::zero(),
            ..inst.valid.clone()
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
        inputs: Vec::new(),
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
    let mut x = valid.clone();
    x.a.1 += Fq::one();
    assert!(x.to_points().is_none());
    let enc = scheme.encode(&ek, &x);
    assert_eq!(
        scheme.eval(&program, &enc, &x),
        Some(SECRET),
        "check on A opens s"
    );

    // B off the twist.
    let mut x = valid.clone();
    x.b.0.c1 += Fq::one();
    assert!(x.to_points().is_none());
    let enc = scheme.encode(&ek, &x);
    assert_eq!(
        scheme.eval(&program, &enc, &x),
        Some(SECRET),
        "check on B opens s"
    );

    // C off the curve.
    let mut x = valid.clone();
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
        ..inst.valid.clone()
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

    let aimed = ProofPoints {
        a,
        ..inst.valid.clone()
    };
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
    let mut off = coords.clone();
    off.a.0 += Fq::one();
    let x = ProofBits::from_coords(&off);
    let enc = scheme.encode(&ek, &x);
    assert_eq!(scheme.eval(&program, &enc, &x), Some(SECRET), "off-curve A");

    // Off-curve B, given as bits.
    let mut off = coords.clone();
    off.b.1.c0 += Fq::one();
    let x = ProofBits::from_coords(&off);
    let enc = scheme.encode(&ek, &x);
    assert_eq!(scheme.eval(&program, &enc, &x), Some(SECRET), "off-twist B");

    // B on the twist but off G_2, given as bits.
    let bad = ProofPoints {
        b: twist_point_off_g2(&mut rng),
        ..inst.valid.clone()
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
    assert_eq!(N_BASE, FieldLayout::new(0).base_field_entries());
    assert_eq!(N_BASE, 10_758);
    assert_eq!(n_base(1), FieldLayout::new(1).base_field_entries());
    assert_eq!(n_base(5), 10_758 + 5 * 128);
}

/// Each statement scalar adds one DFB instance with `κ` labels to the program,
/// and nothing to `f~_G`.
#[test]
fn exact_program_size_with_a_statement_scalar() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 1);
    let scheme = bit_scheme(inst.vk, SID.to_vec());
    let (program, _) = scheme.garble(&mut rng, &SECRET);
    let report = size_report(&program);

    assert_eq!(report.group_bits, 98_432);
    // 905,984 fixed per instance, 611 per label.
    assert_eq!(report.dfb_ciphertext_bits, 13_821_010 + 905_984 + 128 * 611);
    assert_eq!(report.dfb_output_decoding_bits, 6_573_138 + 128 * 611);
    assert_eq!(report.total_bits(), 21_554_980);
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
/// expected per-block instances must disclose nothing rather than
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
        ..inst.valid.clone()
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

// -------------------------------------------------------- variable statement

/// The statement counts covered: one live scalar as in SP1, and several.
const ELLS: [usize; 3] = [1, 2, 5];

/// The same program decides every statement, which is the point of leaving it to
/// the evaluator. Encoding twice under one key is only sound here because the test
/// plays both parties; see `reusing_statement_labels_recovers_the_secret`.
#[test]
fn group_layer_decides_the_statement_online() {
    let mut rng = ark_std::test_rng();
    for ell in ELLS {
        let inst = synthetic_with_inputs(&mut rng, ell);
        let scheme = group_scheme(&inst.vk);
        let (program, ek) = scheme.garble(&mut rng, &SECRET);

        let enc = scheme.encode(&ek, &inst.valid);
        assert_eq!(scheme.eval(&program, &enc, &inst.valid), None, "ell {ell}");

        let enc = scheme.encode(&ek, &inst.invalid);
        assert_eq!(
            scheme.eval(&program, &enc, &inst.invalid),
            Some(SECRET),
            "ell {ell}"
        );

        // A valid proof, but each statement scalar in turn is not the one it proves.
        for i in 0..ell {
            let mut other = inst.valid.clone();
            other.inputs[i] += Fr::one();
            assert!(!inst.vk.is_valid(&other));
            let enc = scheme.encode(&ek, &other);
            assert_eq!(
                scheme.eval(&program, &enc, &other),
                Some(SECRET),
                "ell {ell}, scalar {i}"
            );
        }
    }
}

/// Folding a scalar into `D` and leaving it to the evaluator decide the same proofs.
#[test]
fn group_layer_folded_and_variable_statements_agree() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 2);
    let mut folded = inst.vk.clone();
    let first = inst.vk.input_bases[0] * inst.valid.inputs[0];
    folded.d -= grover::curve::pair(&first, &inst.vk.h2);
    folded.input_bases = inst.vk.input_bases[1..].to_vec();
    let keep = |x: &ProofPoints| ProofPoints {
        inputs: x.inputs[1..].to_vec(),
        ..x.clone()
    };

    let variable = group_scheme(&inst.vk);
    let folded_scheme = group_scheme(&folded);
    let (program_v, ek_v) = variable.garble(&mut rng, &SECRET);
    let (program_f, ek_f) = folded_scheme.garble(&mut rng, &SECRET);
    for (x, want) in [(&inst.valid, None), (&inst.invalid, Some(SECRET))] {
        assert_eq!(folded.is_valid(&keep(x)), inst.vk.is_valid(x));
        let enc = variable.encode(&ek_v, x);
        assert_eq!(variable.eval(&program_v, &enc, x), want);
        let enc = folded_scheme.encode(&ek_f, &keep(x));
        assert_eq!(folded_scheme.eval(&program_f, &enc, &keep(x)), want);
    }
}

/// The labels are masked: none equals `0` or `ξ_i` in the clear, which is what an
/// unmasked `c_t·ξ_i` would be, and no two entries or scalars share an offset.
#[test]
fn group_layer_masks_statement_labels() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 2);
    let scheme = group_scheme(&inst.vk);
    let (_, ek) = scheme.garble(&mut rng, &SECRET);
    let enc = scheme.encode(&ek, &inst.valid);
    let mut seen = std::collections::HashSet::new();
    for (i, labels) in enc.inputs.iter().enumerate() {
        for &z in labels {
            assert!(!z.is_zero() && z != inst.valid.inputs[i]);
        }
    }
    for keys in &ek.input_keys {
        for rho in keys {
            assert!(seen.insert(*rho), "an offset repeats");
        }
    }
}

/// The change of variables behind privacy on a valid proof. After the DDH step the
/// `B` keys are independent `S_t`, and flipping `c_t` by `Δ` while shifting
/// `S_t`, `K^C_t` and `ρ_{i,t}` by `Δ` times the input leaves every label in place
/// and moves `K_t` by `Δ·P`. So on a valid proof the view does not depend on `c_t`,
/// and on an invalid one the shifted key misses the commitment.
#[test]
fn statement_shift_preserves_the_view_exactly_when_the_proof_is_valid() {
    use grover::curve::{h_com, multi_pair, Gt};

    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 2);
    let scheme = group_scheme(&inst.vk);
    let vk = &inst.vk;
    let (program, ek) = scheme.garble(&mut rng, &SECRET);

    let sum_at = |xs: &[Fr]| {
        vk.input_bases
            .iter()
            .zip(xs)
            .fold(G1::zero(), |acc, (b, x)| acc + *b * *x)
    };
    for (x, valid) in [(&inst.valid, true), (&inst.invalid, false)] {
        let enc = scheme.encode(&ek, x);
        let q = enc.a.iter().rev().fold(G1::zero(), |acc, p| acc + acc + *p);
        for t in 0..KAPPA {
            let u = program.bases[t];
            let key = |c: bool, s: Twist, k_c: G1, rho: &[Fr]| -> Gt {
                let base = multi_pair([q, x.a, k_c, sum_at(rho)], [u, s, vk.h1, vk.h2]);
                if c {
                    base + vk.d
                } else {
                    base
                }
            };
            let rho: Vec<Fr> = ek.input_keys.iter().map(|keys| keys[t]).collect();
            let c = ek.coeffs[t];
            let k = key(c, ek.b_keys[t], ek.c_keys[t], &rho);
            assert_eq!(h_com(SID, t, &k), program.commits[t], "the honest key");

            // Flip c_t: Δ = c_t − c'_t.
            let flipped = !c;
            let delta = if c { Fr::one() } else { -Fr::one() };
            let s2 = ek.b_keys[t] + x.b * delta;
            let k_c2 = ek.c_keys[t] + x.c * delta;
            let rho2: Vec<Fr> = rho
                .iter()
                .zip(&x.inputs)
                .map(|(r, xi)| *r + delta * *xi)
                .collect();

            let on = |c: bool, xi: Fr, r: Fr| if c { xi + r } else { r };
            for (i, (xi, r)) in x.inputs.iter().zip(&rho2).enumerate() {
                assert_eq!(on(flipped, *xi, *r), enc.inputs[i][t]);
            }
            let same_b = if flipped { x.b + s2 } else { s2 };
            assert_eq!(same_b, enc.b[t]);
            let same_c = if flipped { x.c + k_c2 } else { k_c2 };
            assert_eq!(same_c, enc.c[t]);

            assert_eq!(key(flipped, s2, k_c2, &rho2) == k, valid, "entry {t}");
        }
    }
}

/// A zero scalar still has labels, `z_{i,t} = ρ_{i,t}`, and they still decode.
#[test]
fn group_layer_handles_a_zero_statement_scalar() {
    let mut rng = ark_std::test_rng();
    let mut inst = synthetic_with_inputs(&mut rng, 1);
    let delta = inst.vk.input_bases[0] * inst.valid.inputs[0];
    inst.vk.d -= grover::curve::pair(&delta, &inst.vk.h2);
    inst.valid.inputs[0] = Fr::zero();
    inst.invalid.inputs[0] = Fr::zero();
    assert!(inst.vk.is_valid(&inst.valid));

    let scheme = group_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);
    let enc = scheme.encode(&ek, &inst.valid);
    assert_eq!(scheme.eval(&program, &enc, &inst.valid), None);
    let enc = scheme.encode(&ek, &inst.invalid);
    assert_eq!(scheme.eval(&program, &enc, &inst.invalid), Some(SECRET));
}

/// Off the subgroup, the labels on `B` open `s` whatever the statement is.
#[test]
fn group_layer_discloses_off_the_subgroup_with_a_statement() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 2);
    let scheme = group_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);
    let bad = ProofPoints {
        b: twist_point_off_g2(&mut rng),
        ..inst.valid.clone()
    };
    let enc = scheme.encode(&ek, &bad);
    assert_eq!(scheme.eval(&program, &enc, &bad), Some(SECRET));
}

/// The labels of two different statements under one key subtract to
/// `c_t·(ξ' − ξ)`, which recovers `c⃗` and the pad without any proof at all. So the
/// surrounding protocol must release the labels of only one statement per garbling.
#[test]
fn reusing_statement_labels_recovers_the_secret() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 1);
    let scheme = group_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);

    let mut other = inst.valid.clone();
    other.inputs[0] += Fr::rand(&mut rng);
    let first = scheme.encode(&ek, &inst.valid);
    let second = scheme.encode(&ek, &other);

    let delta = other.inputs[0] - inst.valid.inputs[0];
    let recovered: Vec<u8> = (0..KAPPA)
        .map(|t| {
            let d = second.inputs[0][t] - first.inputs[0][t];
            assert!(d.is_zero() || d == delta);
            !d.is_zero() as u8
        })
        .collect();
    assert_eq!(xor(&program.ct, &h_key(SID, &recovered)), SECRET);
}

/// A statement of the wrong shape, or a wrong or truncated statement label, must
/// disclose nothing and must not panic.
#[test]
fn group_layer_rejects_malformed_statement_material() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 2);
    let scheme = group_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);
    let enc = scheme.encode(&ek, &inst.invalid);

    let mut short = inst.invalid.clone();
    short.inputs.pop();
    assert_eq!(scheme.eval(&program, &enc, &short), None);
    assert_eq!(inst.vk.verdict(&short), None);

    let mut bad = enc.clone();
    bad.inputs.pop();
    assert_eq!(scheme.eval(&program, &bad, &inst.invalid), None);

    let mut bad = enc.clone();
    bad.inputs[1].pop();
    assert_eq!(scheme.eval(&program, &bad, &inst.invalid), None);

    let mut bad = enc.clone();
    bad.inputs[0][3] += Fr::one();
    assert_eq!(scheme.eval(&program, &bad, &inst.invalid), None);
}

#[test]
#[should_panic(expected = "one statement scalar per garbled input")]
fn group_layer_refuses_to_encode_the_wrong_statement_shape() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 2);
    let scheme = group_scheme(&inst.vk);
    let (_, ek) = scheme.garble(&mut rng, &SECRET);
    let mut short = inst.valid.clone();
    short.inputs.pop();
    let _ = scheme.encode(&ek, &short);
}

#[test]
fn field_layer_decides_the_statement_online() {
    let mut rng = ark_std::test_rng();
    for ell in ELLS {
        let inst = synthetic_with_inputs(&mut rng, ell);
        let scheme = field_scheme(&inst.vk);
        let (program, ek) = scheme.garble(&mut rng, &SECRET);

        let valid = ProofCoords::from_points(&inst.valid).unwrap();
        let enc = scheme.encode(&ek, &valid);
        assert_eq!(scheme.eval(&program, &enc, &valid), None, "ell {ell}");

        let mut other = valid.clone();
        other.inputs[ell - 1] += Fr::one();
        let enc = scheme.encode(&ek, &other);
        assert_eq!(
            scheme.eval(&program, &enc, &other),
            Some(SECRET),
            "ell {ell}"
        );

        // Off-curve discloses through the curve check, with the statement present.
        let mut off = valid.clone();
        off.a.1 += Fq::one();
        let enc = scheme.encode(&ek, &off);
        assert_eq!(scheme.eval(&program, &enc, &off), Some(SECRET), "ell {ell}");
    }
}

#[test]
fn field_layer_discloses_on_a_proof_aimed_at_the_masks_with_a_statement() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 1);
    let scheme = field_scheme(&inst.vk);
    let (program, ek_f, ek_g) = scheme.garble_parts(&mut rng, &SECRET);
    let i = ek_g.a_coeffs.iter().position(|&c| c).unwrap();
    let aimed = ProofPoints {
        a: ek_g.a_keys[i],
        ..inst.valid.clone()
    };
    let x = ProofCoords::from_points(&aimed).unwrap();
    let enc = scheme.encode(&ek_f, &x);
    assert_eq!(scheme.eval(&program, &enc, &x), Some(SECRET));
}

#[test]
fn field_layer_rejects_malformed_statement_material() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 1);
    let scheme = field_scheme(&inst.vk);
    let (program, ek) = scheme.garble(&mut rng, &SECRET);
    let x = ProofCoords::from_points(&inst.invalid).unwrap();
    let enc = scheme.encode(&ek, &x);

    let mut short = x.clone();
    short.inputs.clear();
    assert_eq!(scheme.eval(&program, &enc, &short), None);

    let mut bad = enc.clone();
    bad.inputs.clear();
    assert_eq!(scheme.eval(&program, &bad, &x), None);

    let mut bad = enc.clone();
    bad.inputs[0].pop();
    assert_eq!(scheme.eval(&program, &bad, &x), None);
}

#[test]
fn bit_layer_decides_the_statement_online() {
    let mut rng = ark_std::test_rng();
    for ell in ELLS {
        let inst = synthetic_with_inputs(&mut rng, ell);
        let scheme = bit_scheme(inst.vk.clone(), SID.to_vec());
        let (program, ek) = scheme.garble(&mut rng, &SECRET);
        assert_eq!(program.1.instances.len(), 8 + ell);

        let coords = ProofCoords::from_points(&inst.valid).unwrap();
        let valid = ProofBits::from_coords(&coords);
        assert_eq!(BinToField.apply(&valid), coords);
        let enc = scheme.encode(&ek, &valid);
        assert_eq!(scheme.eval(&program, &enc, &valid), None, "ell {ell}");

        let mut other = coords.clone();
        other.inputs[0] += Fr::one();
        let other = ProofBits::from_coords(&other);
        let enc = scheme.encode(&ek, &other);
        assert_eq!(
            scheme.eval(&program, &enc, &other),
            Some(SECRET),
            "ell {ell}"
        );

        let invalid = ProofBits::from_coords(&ProofCoords::from_points(&inst.invalid).unwrap());
        let enc = scheme.encode(&ek, &invalid);
        assert_eq!(
            scheme.eval(&program, &enc, &invalid),
            Some(SECRET),
            "ell {ell}"
        );
    }
}

/// `ι_bin` reduces a statement block modulo `r`: the block of `ξ + r` describes the
/// same statement and seals, like a coordinate plus `p`. A deployed verifier would
/// reject it instead.
#[test]
fn bit_layer_reduces_a_non_canonical_statement_block() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 1);
    let scheme = bit_scheme(inst.vk.clone(), SID.to_vec());
    let (program, ek) = scheme.garble(&mut rng, &SECRET);
    let coords = ProofCoords::from_points(&inst.valid).unwrap();
    let mut x = ProofBits::from_coords(&coords);

    let mut big = coords.inputs[0].into_bigint();
    if big.add_with_carry(&Fr::MODULUS) {
        panic!("ξ + r fits in 256 bits");
    }
    x.inputs[0].copy_from_slice(&big.to_bytes_le()[..32]);
    assert_ne!(x.inputs[0], fr_to_block(coords.inputs[0]));
    assert_eq!(BinToField.apply(&x), coords);

    let enc = scheme.encode(&ek, &x);
    assert_eq!(scheme.eval(&program, &enc, &x), None);

    // A valid proof returns before reading the labels, so check that they decode
    // through a block above `r` on an invalid proof.
    let mut bad = ProofBits::from_coords(&ProofCoords::from_points(&inst.invalid).unwrap());
    bad.inputs[0] = x.inputs[0];
    let enc = scheme.encode(&ek, &bad);
    assert_eq!(scheme.eval(&program, &enc, &bad), Some(SECRET));
}

/// A block near `2^256`, far above `r`, decodes through the smudging without
/// wrapping the CRT modulus.
#[test]
fn bit_layer_decodes_the_largest_statement_block() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 1);
    let scheme = bit_scheme(inst.vk.clone(), SID.to_vec());
    let (program, ek) = scheme.garble(&mut rng, &SECRET);
    let mut x = ProofBits::from_coords(&ProofCoords::from_points(&inst.valid).unwrap());
    x.inputs[0] = [0xFF; 32];
    let enc = scheme.encode(&ek, &x);
    // All-ones is not the statement this proof is for.
    assert_eq!(scheme.eval(&program, &enc, &x), Some(SECRET));
}

#[test]
fn bit_layer_rejects_a_missing_statement_instance() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 1);
    let scheme = bit_scheme(inst.vk.clone(), SID.to_vec());
    let (mut program, ek) = scheme.garble(&mut rng, &SECRET);
    let invalid = ProofBits::from_coords(&ProofCoords::from_points(&inst.invalid).unwrap());
    let enc = scheme.encode(&ek, &invalid);

    // The evaluator's statement has the wrong shape for the program.
    let mut short = invalid.clone();
    short.inputs.clear();
    assert_eq!(scheme.eval(&program, &enc, &short), None);

    program.1.instances.pop();
    assert_eq!(scheme.eval(&program, &enc, &invalid), None);
}

#[test]
#[should_panic(expected = "aggregate target")]
fn bit_scheme_refuses_too_many_statement_scalars() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, grover::bits::MAX_INPUTS + 1);
    let _ = bit_scheme(inst.vk, SID.to_vec());
}

#[test]
fn bit_layer_runs_at_the_largest_statement() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, grover::bits::MAX_INPUTS);
    let scheme = bit_scheme(inst.vk.clone(), SID.to_vec());
    let (program, ek) = scheme.garble(&mut rng, &SECRET);
    let valid = ProofBits::from_coords(&ProofCoords::from_points(&inst.valid).unwrap());
    let enc = scheme.encode(&ek, &valid);
    assert_eq!(scheme.eval(&program, &enc, &valid), None);
    let invalid = ProofBits::from_coords(&ProofCoords::from_points(&inst.invalid).unwrap());
    let enc = scheme.encode(&ek, &invalid);
    assert_eq!(scheme.eval(&program, &enc, &invalid), Some(SECRET));
}

/// More statement blocks than the program has instances, or the reverse, disclose
/// nothing rather than panic.
#[test]
fn bit_layer_rejects_extra_statement_material() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 1);
    let scheme = bit_scheme(inst.vk.clone(), SID.to_vec());
    let (program, ek) = scheme.garble(&mut rng, &SECRET);
    let invalid = ProofBits::from_coords(&ProofCoords::from_points(&inst.invalid).unwrap());
    let enc = scheme.encode(&ek, &invalid);

    let mut long = invalid.clone();
    long.inputs.push([0u8; 32]);
    assert_eq!(scheme.eval(&program, &enc, &long), None);

    // A program garbled for two scalars, evaluated against a statement of one.
    let wider = synthetic_with_inputs(&mut rng, 2);
    let (other, _) = bit_scheme(wider.vk, SID.to_vec()).garble(&mut rng, &SECRET);
    assert_eq!(scheme.eval(&other, &enc, &invalid), None);
}

#[test]
#[should_panic(expected = "one statement scalar per garbled input")]
fn field_layer_refuses_to_encode_the_wrong_statement_shape() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 1);
    let scheme = field_scheme(&inst.vk);
    let (_, ek) = scheme.garble(&mut rng, &SECRET);
    let mut short = ProofCoords::from_points(&inst.valid).unwrap();
    short.inputs.clear();
    let _ = scheme.encode(&ek, &short);
}

#[test]
#[should_panic(expected = "one statement scalar per garbled input")]
fn bit_layer_refuses_to_encode_the_wrong_statement_shape() {
    let mut rng = ark_std::test_rng();
    let inst = synthetic_with_inputs(&mut rng, 1);
    let scheme = bit_scheme(inst.vk.clone(), SID.to_vec());
    let (_, ek) = scheme.garble(&mut rng, &SECRET);
    let mut short = ProofBits::from_coords(&ProofCoords::from_points(&inst.valid).unwrap());
    short.inputs.clear();
    let _ = scheme.encode(&ek, &short);
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
