//! The scheme over bits on a Groth16 proof in SP1's wire format: a gnark-compressed
//! proof, and a statement whose only value not known at garbling time is
//! `committed_values_digest`, the masked blake3 hash of the program's public values.
//! The other public inputs are folded and the digest is left to the evaluator.
//!
//! The fixture is a mock, not a proof from SP1 itself: the key, proof and public
//! values of `test_groth16_verify_compressed_true_small_using_mock_sp1_proof_in_gnark_format`
//! in the `g16` repository (`g16ckt/src/gadgets/groth16.rs`). It has two public
//! inputs, the vkey hash and the digest. SP1 v6 has three more that are folded the
//! same way, a pattern `tests/groth16.rs` covers on a five-input circuit.

mod common;

use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ff::{BigInteger, Field, PrimeField, Zero};
use ark_groth16::{Groth16, Proof, VerifyingKey};
use ark_serialize::CanonicalDeserialize;
use ark_snark::SNARK;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use common::{points_with_inputs_from_ark, variable_verifier_from_ark, verifier_from_ark};
use grover::bit_scheme;
use grover::bits::ProofBits;
use grover::curve::{b1, b2, block_to_fr, fr_to_block, Secret};
use grover::field::ProofCoords;
use grover::group::ProofPoints;
use grover::pgs::Pgs;
use std::str::FromStr;

const VK_BYTES: [u8; 328] = [
    226, 242, 109, 190, 162, 153, 245, 34, 59, 100, 108, 177, 251, 51, 234, 219, 5, 157, 148, 7,
    85, 157, 116, 65, 223, 217, 2, 227, 167, 154, 77, 45, 171, 183, 61, 193, 127, 188, 19, 2, 30,
    36, 113, 224, 192, 139, 214, 125, 132, 1, 245, 43, 115, 214, 208, 116, 131, 121, 76, 173, 71,
    120, 24, 14, 12, 6, 243, 59, 188, 76, 121, 169, 202, 222, 242, 83, 166, 128, 132, 211, 130,
    241, 119, 136, 248, 133, 201, 175, 209, 118, 247, 203, 47, 3, 103, 137, 237, 246, 146, 217, 92,
    189, 222, 70, 221, 218, 94, 247, 212, 34, 67, 103, 121, 68, 92, 94, 102, 0, 106, 66, 118, 30,
    31, 18, 239, 222, 0, 24, 194, 18, 243, 174, 183, 133, 228, 151, 18, 231, 169, 53, 51, 73, 170,
    241, 37, 93, 251, 49, 183, 191, 96, 114, 58, 72, 13, 146, 147, 147, 142, 25, 237, 34, 1, 251,
    191, 54, 215, 39, 179, 99, 122, 119, 118, 59, 61, 248, 184, 228, 40, 77, 53, 39, 175, 44, 254,
    55, 12, 186, 244, 65, 255, 3, 230, 116, 95, 132, 105, 130, 153, 33, 69, 2, 32, 192, 12, 94,
    134, 224, 54, 210, 70, 155, 204, 30, 240, 33, 95, 103, 21, 231, 141, 203, 199, 156, 3, 0, 0, 0,
    0, 0, 0, 0, 142, 117, 169, 138, 181, 40, 29, 69, 76, 115, 219, 51, 146, 119, 36, 245, 235, 67,
    55, 205, 148, 166, 160, 78, 138, 173, 176, 175, 28, 30, 9, 38, 76, 251, 81, 137, 196, 193, 55,
    229, 85, 135, 135, 236, 198, 54, 237, 80, 167, 204, 144, 208, 39, 194, 7, 38, 93, 162, 61, 253,
    208, 63, 28, 6, 28, 231, 41, 209, 79, 99, 32, 224, 222, 40, 96, 161, 81, 236, 253, 79, 236,
    178, 208, 234, 226, 224, 224, 127, 129, 121, 138, 56, 65, 178, 234, 4,
];

const PROOF_BYTES: [u8; 128] = [
    170, 12, 19, 111, 213, 193, 180, 194, 24, 97, 133, 134, 142, 65, 68, 80, 167, 234, 134, 227,
    122, 69, 42, 179, 185, 45, 72, 68, 52, 31, 126, 55, 142, 161, 94, 118, 133, 222, 93, 107, 124,
    105, 240, 163, 172, 101, 196, 1, 93, 161, 93, 136, 222, 36, 67, 217, 126, 98, 135, 154, 172,
    13, 119, 39, 42, 176, 232, 63, 74, 70, 162, 89, 95, 2, 203, 110, 153, 130, 190, 30, 2, 169, 82,
    97, 127, 41, 178, 126, 100, 122, 6, 163, 63, 123, 193, 142, 195, 12, 126, 179, 148, 173, 40,
    196, 73, 211, 203, 24, 113, 50, 95, 124, 195, 7, 248, 1, 160, 57, 234, 184, 171, 0, 145, 121,
    136, 61, 232, 165,
];

const PUBLIC_VALUES: [u8; 36] = [
    55, 0, 0, 0, 3, 0, 0, 0, 5, 0, 0, 0, 8, 0, 0, 0, 13, 0, 0, 0, 21, 0, 0, 0, 34, 0, 0, 0, 55, 0,
    0, 0, 89, 0, 0, 0,
];

const SP1_VKEY_HASH: &str =
    "71453366410619949346755464650355874340577815840172820125756847035126066871";

/// `committed_values_digest`: blake3 of the public values, big-endian, with the top
/// three bits cleared so that it fits in `F_r`.
fn digest_of(public_values: &[u8]) -> Fr {
    let mut digest = *blake3::hash(public_values).as_bytes();
    digest[0] &= 0x1F;
    Fr::from_be_bytes_mod_order(&digest)
}

/// Whether `y` is the lexicographically larger of `±y`.
fn is_larger(y: Fq) -> bool {
    y.into_bigint() > (-y).into_bigint()
}

/// Whether `y` is the lexicographically larger of `±y`, on `c1` and then `c0`.
fn is_larger_fq2(y: Fq2) -> bool {
    if y.c1.is_zero() {
        is_larger(y.c0)
    } else {
        is_larger(y.c1)
    }
}

/// The gnark flags on a compressed point, smaller and larger `y`.
const SMALLER: u8 = 0b10;
const LARGER: u8 = 0b11;

/// A big-endian base-field element whose top two bits are gnark's compression flag.
fn fq_with_flag(bytes: &[u8]) -> (Fq, u8) {
    let flag = bytes[0] >> 6;
    assert!(flag == SMALLER || flag == LARGER, "not a compressed point");
    let mut raw = bytes.to_vec();
    raw[0] &= 0x3F;
    (Fq::from_be_bytes_mod_order(&raw), flag)
}

fn g1_from_gnark(bytes: &[u8]) -> G1Affine {
    let (x, flag) = fq_with_flag(bytes);
    let y = (x * x * x + b1()).sqrt().expect("x is on the curve");
    let y = if is_larger(y) == (flag == LARGER) {
        y
    } else {
        -y
    };
    G1Affine::new(x, y)
}

fn g2_from_gnark(bytes: &[u8]) -> G2Affine {
    let (c1, flag) = fq_with_flag(&bytes[..32]);
    let c0 = Fq::from_be_bytes_mod_order(&bytes[32..]);
    let x = Fq2::new(c0, c1);
    let y = (x * x * x + b2()).sqrt().expect("x is on the twist");
    let y = if is_larger_fq2(y) == (flag == LARGER) {
        y
    } else {
        -y
    };
    G2Affine::new(x, y)
}

fn proof() -> Proof<Bn254> {
    Proof {
        a: g1_from_gnark(&PROOF_BYTES[..32]),
        b: g2_from_gnark(&PROOF_BYTES[32..96]),
        c: g1_from_gnark(&PROOF_BYTES[96..]),
    }
}

fn verifying_key() -> VerifyingKey<Bn254> {
    VerifyingKey::deserialize_compressed(&VK_BYTES[..]).unwrap()
}

fn vkey_hash() -> Fr {
    Fr::from_str(SP1_VKEY_HASH).unwrap()
}

fn bits_of(x: &ProofPoints) -> ProofBits {
    ProofBits::from_coords(&ProofCoords::from_points(x).unwrap())
}

/// The fixture is what we think it is, before any of the scheme is involved.
#[test]
fn fixture_verifies_under_ark_groth16() {
    let vk = verifying_key();
    assert_eq!(vk.gamma_abc_g1.len(), 3, "the vkey hash and the digest");
    assert_eq!(PUBLIC_VALUES.len(), 36);

    let proof = proof();
    let digest = digest_of(&PUBLIC_VALUES);
    assert!(Groth16::<Bn254>::verify(&vk, &[vkey_hash(), digest], &proof).unwrap());
    let other = digest + Fr::from(1u64);
    assert!(!Groth16::<Bn254>::verify(&vk, &[vkey_hash(), other], &proof).unwrap());
}

/// One garbling for the program, with no public values in mind: the digest is an
/// evaluator input. The proof seals for the digest of its own public values and
/// discloses for the digest of any others.
#[test]
fn one_garbling_decides_the_digest() {
    let vk = verifying_key();
    let proof = proof();
    let scheme = bit_scheme(
        variable_verifier_from_ark(&vk, &[Some(vkey_hash()), None]),
        b"sp1".to_vec(),
    );
    assert_eq!(scheme.outer.group.vk.input_bases.len(), 1);

    let mut rng = StdRng::seed_from_u64(1);
    let secret: Secret = [0xC3; 16];
    let (program, ek) = scheme.garble(&mut rng, &secret);

    let own = points_with_inputs_from_ark(&proof, &[digest_of(&PUBLIC_VALUES)]);
    assert!(scheme.outer.group.vk.is_valid(&own));
    let bits = bits_of(&own);
    let enc = scheme.encode(&ek, &bits);
    assert_eq!(scheme.eval(&program, &enc, &bits), None);

    let mut other_values = PUBLIC_VALUES;
    other_values[0] ^= 1;
    let other = points_with_inputs_from_ark(&proof, &[digest_of(&other_values)]);
    assert!(!scheme.outer.group.vk.is_valid(&other));
    let bits = bits_of(&other);
    let enc = scheme.encode(&ek, &bits);
    assert_eq!(scheme.eval(&program, &enc, &bits), Some(secret));
}

/// The digest fits in 253 bits, so its block is canonical, and the block is the
/// masked hash with its bytes reversed. This pins the bit order the evaluator's
/// labels must be released in.
#[test]
fn digest_block_is_the_reversed_hash() {
    let digest = digest_of(&PUBLIC_VALUES);
    let block = fr_to_block(digest);
    assert_eq!(block_to_fr(&block), digest);
    assert!(digest.into_bigint().num_bits() <= 253);

    let mut raw = *blake3::hash(&PUBLIC_VALUES).as_bytes();
    raw[0] &= 0x1F;
    raw.reverse();
    assert_eq!(block, raw);
}

/// Folding the digest as well, for a garbling per set of public values, decides the
/// same proof the same way.
#[test]
fn folding_the_digest_agrees() {
    let vk = verifying_key();
    let proof = proof();
    let digest = digest_of(&PUBLIC_VALUES);
    let scheme = bit_scheme(
        verifier_from_ark(&vk, &[vkey_hash(), digest]),
        b"sp1-folded".to_vec(),
    );
    let mut rng = StdRng::seed_from_u64(2);
    let secret: Secret = [0xC3; 16];
    let (program, ek) = scheme.garble(&mut rng, &secret);
    let bits = bits_of(&points_with_inputs_from_ark(&proof, &[]));
    let enc = scheme.encode(&ek, &bits);
    assert_eq!(scheme.eval(&program, &enc, &bits), None);

    let wrong = bit_scheme(
        verifier_from_ark(&vk, &[vkey_hash(), digest + Fr::from(1u64)]),
        b"sp1-folded".to_vec(),
    );
    let (program, ek) = wrong.garble(&mut rng, &secret);
    let enc = wrong.encode(&ek, &bits);
    assert_eq!(wrong.eval(&program, &enc, &bits), Some(secret));
}
