//! BN254 as the draft uses it: the two source groups, the twist, the curve
//! equations, the pairing in additive notation, and the two hash functions.
//!
//! `G_1 = E(F_p)` has prime order `r`, so a pair of coordinates on `E` is a group
//! element. The twist `E'(F_{p^2})` has order `r·h_2`, and `G_2` is its unique
//! subgroup of order `r`; a pair of coordinates on `E'` is a twist point that
//! lies in `G_2` only if `r·B = O`. We therefore type twist points as [`Twist`]
//! and check membership with [`in_g2`].

use ark_bn254::{
    g1::Config as G1Config, g2::Config as G2Config, Bn254, Fq, Fq2, Fr, G1Affine, G1Projective,
    G2Affine, G2Projective,
};
use ark_ec::{
    pairing::{Pairing, PairingOutput},
    short_weierstrass::SWCurveConfig,
    CurveGroup, PrimeGroup,
};
use ark_ff::{BigInteger, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use sha2::{Digest, Sha256};

/// The group `G_1 = E(F_p)`.
pub type G1 = G1Projective;
/// A point of the twist `E'(F_{p^2})`, not necessarily in `G_2`.
pub type Twist = G2Projective;
/// The target group, written additively.
pub type Gt = PairingOutput<Bn254>;

/// The security parameter `λ`.
pub const LAMBDA: usize = 128;
/// The garbler's secret, `λ` bits.
pub type Secret = [u8; LAMBDA / 8];

/// The pairing `e: G_1 × G_2 → G_T`. The caller guarantees `b ∈ G_2`.
pub fn pair(a: &G1, b: &Twist) -> Gt {
    Bn254::pairing(*a, *b)
}

/// `e(a_1, b_1) + ... + e(a_N, b_N)`, with one final exponentiation instead of
/// `N`. Same value, cheaper. The caller guarantees every `b_i ∈ G_2`.
pub fn multi_pair<const N: usize>(a: [G1; N], b: [Twist; N]) -> Gt {
    Bn254::multi_pairing(a, b)
}

/// The constant `b` of `E: v² = u³ + b` over `F_p`.
pub fn b1() -> Fq {
    <G1Config as SWCurveConfig>::COEFF_B
}

/// The constant `b'` of the twist `E': v² = u³ + b'` over `F_{p^2}`.
pub fn b2() -> Fq2 {
    <G2Config as SWCurveConfig>::COEFF_B
}

/// `g_1(u, v) = v² − u³ − b`, zero exactly on the points of `E`.
pub fn g1_eq(u: Fq, v: Fq) -> Fq {
    v * v - u * u * u - b1()
}

/// `g_2(u, v) = v² − u³ − b'`, zero exactly on the points of `E'`.
pub fn g2_eq(u: Fq2, v: Fq2) -> Fq2 {
    v * v - u * u * u - b2()
}

/// `r · B`, computed with the integer `r` (a scalar in `F_r` would reduce to zero).
pub fn r_times(b: &Twist) -> Twist {
    b.mul_bigint(Fr::MODULUS.0)
}

/// Whether a twist point lies in `G_2`.
pub fn in_g2(b: &Twist) -> bool {
    r_times(b).is_zero()
}

/// The point of `E` with the given coordinates, if they satisfy the equation.
pub fn g1_from_coords(u: Fq, v: Fq) -> Option<G1> {
    let a = G1Affine::new_unchecked(u, v);
    a.is_on_curve().then(|| a.into())
}

/// The twist point with the given coordinates, if they satisfy the equation.
pub fn twist_from_coords(u: Fq2, v: Fq2) -> Option<Twist> {
    let a = G2Affine::new_unchecked(u, v);
    a.is_on_curve().then(|| a.into())
}

/// Affine coordinates of a point of `G_1`, or `None` for the point at infinity.
pub fn g1_coords(p: &G1) -> Option<(Fq, Fq)> {
    let a = p.into_affine();
    (!a.infinity).then_some((a.x, a.y))
}

/// Affine coordinates of a twist point, or `None` for the point at infinity.
pub fn twist_coords(p: &Twist) -> Option<(Fq2, Fq2)> {
    let a = p.into_affine();
    (!a.infinity).then_some((a.x, a.y))
}

/// `H(sid, t, K)`: a commitment to a target-group element. The output is the
/// full 256 bits of SHA-256, that is `τ = 2λ`, to secure against a party choosing inputs
/// after setup.
pub fn h_com(sid: &[u8], t: usize, n: &Gt) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"grover/H_com");
    h.update((sid.len() as u64).to_le_bytes());
    h.update(sid);
    h.update((t as u64).to_le_bytes());
    let mut bytes = Vec::new();
    n.serialize_compressed(&mut bytes)
        .expect("serializing a target-group element cannot fail");
    h.update(&bytes);
    h.finalize().into()
}

/// `H(sid, c)`: the one-time pad on the secret, derived from the coefficient
/// vector, one byte per coefficient.
pub fn h_key(sid: &[u8], coeffs: &[u8]) -> Secret {
    let mut h = Sha256::new();
    h.update(b"grover/H_key");
    h.update((sid.len() as u64).to_le_bytes());
    h.update(sid);
    h.update((coeffs.len() as u64).to_le_bytes());
    h.update(coeffs);
    let digest = h.finalize();
    let mut out = [0u8; LAMBDA / 8];
    out.copy_from_slice(&digest[..LAMBDA / 8]);
    out
}

/// One-time pad.
pub fn xor(a: &Secret, b: &Secret) -> Secret {
    let mut out = [0u8; LAMBDA / 8];
    for i in 0..LAMBDA / 8 {
        out[i] = a[i] ^ b[i];
    }
    out
}

/// The secret read as an element of `F_p`. Since `λ < lg p`, no reduction occurs.
pub fn secret_to_fq(s: &Secret) -> Fq {
    Fq::from_le_bytes_mod_order(s)
}

/// The inverse of [`secret_to_fq`]: `None` if the element does not fit in `λ` bits.
pub fn fq_to_secret(x: Fq) -> Option<Secret> {
    let bytes = x.into_bigint().to_bytes_le();
    if bytes[LAMBDA / 8..].iter().any(|&b| b != 0) {
        return None;
    }
    let mut out = [0u8; LAMBDA / 8];
    out.copy_from_slice(&bytes[..LAMBDA / 8]);
    Some(out)
}

/// The base-field prime `p` as little-endian limbs.
pub fn p_limbs() -> [u64; 4] {
    Fq::MODULUS.0
}

/// An `F_p` element as little-endian limbs.
pub fn fq_limbs(x: Fq) -> [u64; 4] {
    x.into_bigint().0
}

/// A little-endian 256-bit block as an element of `F_p`, reduced modulo `p`.
/// This is the map `ι_bin` on one block.
pub fn block_to_fq(block: &[u8; 32]) -> Fq {
    Fq::from_le_bytes_mod_order(block)
}

/// The canonical 256-bit block of an `F_p` element.
pub fn fq_to_block(x: Fq) -> [u8; 32] {
    let bytes = x.into_bigint().to_bytes_le();
    let mut out = [0u8; 32];
    out.copy_from_slice(&bytes[..32]);
    out
}
