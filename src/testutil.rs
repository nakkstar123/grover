//! A synthetic verifier with a matched valid proof, for the tests, and a twist
//! point outside `G_2`.

use crate::curve::{b2, pair, Twist, G1};
use crate::group::{ProofPoints, Verifier};
use ark_bn254::{Fq2, Fr, G2Affine};
use ark_ec::{AffineRepr, PrimeGroup};
use ark_ff::{Field, One, UniformRand};
use ark_std::rand::RngCore;

/// A verifier with a matched valid proof and an invalid one.
pub struct Instance {
    /// The normalized verifier.
    pub vk: Verifier,
    /// A proof it accepts.
    pub valid: ProofPoints,
    /// A proof it rejects.
    pub invalid: ProofPoints,
}

/// Choose `D` so that the proof with discrete logarithms `(a, b, c)` verifies; the
/// invalid proof bumps `a`.
pub fn synthetic(rng: &mut impl RngCore) -> Instance {
    let g1 = G1::generator();
    let g2 = Twist::generator();
    let (a, b, c, eta) = (Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng));
    let h1 = g2 * eta;
    let mk = |aa: Fr| ProofPoints {
        a: g1 * aa,
        b: g2 * b,
        c: g1 * c,
    };
    let valid = mk(a);
    let d = pair(&valid.a, &valid.b) + pair(&valid.c, &h1);
    let vk = Verifier { h1, d };
    let invalid = mk(a + Fr::one());
    assert!(vk.is_valid(&valid));
    assert!(!vk.is_valid(&invalid));
    Instance { vk, valid, invalid }
}

/// A point of the twist that is not in `G_2`.
pub fn twist_off_g2(rng: &mut impl RngCore) -> Twist {
    loop {
        let x = Fq2::rand(rng);
        let rhs = x * x * x + b2();
        if let Some(y) = rhs.sqrt() {
            let p = G2Affine::new_unchecked(x, y);
            if p.is_on_curve() && !p.is_in_correct_subgroup_assuming_on_curve() {
                return p.into_group();
            }
        }
    }
}
