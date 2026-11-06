//! Shared test helpers. The synthetic instance and the off-subgroup twist point
//! live in the crate, so that its own unit tests can use them too.

#![allow(dead_code, unused_imports)]

pub use grover::testutil::{synthetic, synthetic_with_inputs, twist_off_g2 as twist_point_off_g2};

use ark_bn254::{Bn254, Fr};
use ark_ec::AffineRepr;
use grover::curve::{pair, G1};
use grover::group::{ProofPoints, Verifier};

/// The normalized verifier for an `ark-groth16` key and a claimed statement:
/// `H_1 = −δ`, `D = e(α, β) + e(X, γ)` with `X = vk_0 + Σ ξ_i vk_i`.
pub fn verifier_from_ark(vk: &ark_groth16::VerifyingKey<Bn254>, statement: &[Fr]) -> Verifier {
    let fixed: Vec<Option<Fr>> = statement.iter().copied().map(Some).collect();
    variable_verifier_from_ark(vk, &fixed)
}

/// The normalized verifier with part of the statement left to the evaluator:
/// `Some(ξ_i)` folds `ξ_i·vk_i` into `D`, `None` keeps `vk_i` as an input base.
pub fn variable_verifier_from_ark(
    vk: &ark_groth16::VerifyingKey<Bn254>,
    statement: &[Option<Fr>],
) -> Verifier {
    let mut x0: G1 = vk.gamma_abc_g1[0].into_group();
    let mut input_bases = Vec::new();
    for (i, xi) in statement.iter().enumerate() {
        let vk_i = vk.gamma_abc_g1[i + 1].into_group();
        match xi {
            Some(xi) => x0 += vk_i * *xi,
            None => input_bases.push(vk_i),
        }
    }
    Verifier {
        h1: -vk.delta_g2.into_group(),
        h2: -vk.gamma_g2.into_group(),
        input_bases,
        d: pair(&vk.alpha_g1.into_group(), &vk.beta_g2.into_group())
            + pair(&x0, &vk.gamma_g2.into_group()),
    }
}

/// An `ark-groth16` proof as points, with a fixed statement.
pub fn points_from_ark(proof: &ark_groth16::Proof<Bn254>) -> ProofPoints {
    points_with_inputs_from_ark(proof, &[])
}

/// An `ark-groth16` proof as points, with the statement scalars left to the
/// evaluator.
pub fn points_with_inputs_from_ark(
    proof: &ark_groth16::Proof<Bn254>,
    inputs: &[Fr],
) -> ProofPoints {
    ProofPoints {
        a: proof.a.into_group(),
        b: proof.b.into_group(),
        c: proof.c.into_group(),
        inputs: inputs.to_vec(),
    }
}
