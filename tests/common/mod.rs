//! Shared test helpers. The synthetic instance and the off-subgroup twist point
//! live in the crate, so that its own unit tests can use them too.

#![allow(dead_code, unused_imports)]

pub use grover::testutil::{synthetic, twist_off_g2 as twist_point_off_g2};

use ark_bn254::{Bn254, Fr};
use ark_ec::AffineRepr;
use grover::curve::{pair, G1};
use grover::group::{ProofPoints, Verifier};

/// The normalized verifier for an `ark-groth16` key and a claimed statement:
/// `H_1 = −δ`, `D = e(α, β) + e(X, γ)` with `X = vk_0 + Σ ξ_i vk_i`.
pub fn verifier_from_ark(vk: &ark_groth16::VerifyingKey<Bn254>, statement: &[Fr]) -> Verifier {
    let mut x: G1 = vk.gamma_abc_g1[0].into_group();
    for (i, xi) in statement.iter().enumerate() {
        x += vk.gamma_abc_g1[i + 1].into_group() * *xi;
    }
    Verifier {
        h1: -vk.delta_g2.into_group(),
        d: pair(&vk.alpha_g1.into_group(), &vk.beta_g2.into_group())
            + pair(&x, &vk.gamma_g2.into_group()),
    }
}

/// An `ark-groth16` proof as points.
pub fn points_from_ark(proof: &ark_groth16::Proof<Bn254>) -> ProofPoints {
    ProofPoints {
        a: proof.a.into_group(),
        b: proof.b.into_group(),
        c: proof.c.into_group(),
    }
}
