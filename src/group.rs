//! `Π_G`: the scheme over groups, for binary coefficients.
//!
//! The evaluator's input is a proof `(A, B, C)`, `A, C ∈ G_1`, `B` on the twist;
//! the garbler's input is the secret `s`. Each point gets an Argo encoding:
//! `n = 254` entries for `A` (coefficients the binary digits of `−k`), `κ = 128`
//! entries each for `B` and `C` (coefficients the shared vector `c⃗`). The keys
//! of `B` share the scalar `k` across bases `U_t`: `K^B_t = k·U_t`. The program
//! is the bases, the commitments `h_t = H(sid, t, K_t)` to
//! `K_t = e(R, U_t) + e(K^C_t, H_1) + c_t·D`, and the pad `ct = s ⊕ H(sid, c⃗)`.
//!
//! Evaluation: if `r·B ≠ O`, then `B ∉ G_2` and the encoding of `B` leaks `c⃗`
//! via `r·⟦B⟧_t = c_t·(r·B)`. Otherwise compute `P = e(A,B) + e(C,H_1) − D`;
//! `P = 0` gives `⊥`, else `Q = Σ 2^i·⟦A⟧_i = −k·A + R` and
//! `Y_t = e(A, ⟦B⟧_t) + e(Q, U_t) + e(⟦C⟧_t, H_1) = c_t·P + K_t` singles out
//! `c_t` against the commitment, and `s` is opened.
//!
//! `U_t`, `M_i`, `K^C_t` are sampled uniformly over the whole group (identity
//! included), matching the theorem exactly: shifting a uniform mask by a fixed
//! constant is uniform regardless of `c`. `k` is sampled away from zero instead,
//! since it is shared multiplicatively across every `B`-entry: `k = 0` would
//! collapse `K^B_t = O` for all `t` at once, exposing the whole vector `c⃗` in
//! one correlated step rather than as a per-entry statistical term.

use crate::curve::{h_com, h_key, in_g2, multi_pair, r_times, xor, Gt, Secret, Twist, G1};
use crate::pgs::Pgs;
use ark_bn254::Fr;
use ark_ff::{AdditiveGroup, BigInteger, PrimeField, UniformRand, Zero};
use ark_std::rand::RngCore;

/// `n`, the number of entries on `A`: the binary digits of a scalar, `⌈lg r⌉`.
pub const N: usize = 254;
/// `κ`, the number of entries on `B` and on `C`: `⌈λ / lg 2⌉ = λ` for binary
/// coefficients.
pub const KAPPA: usize = 128;

/// The fixed data of the Groth16 verifier, normalized so that a proof is valid
/// iff `e(A, B) + e(C, H_1) − D = 0`. With the statement fixed at garbling time,
/// `H_1 = −δ` and `D = e(α, β) + e(X, γ)`.
#[derive(Clone, Debug)]
pub struct Verifier {
    /// The element of `G_2` paired with `C`.
    pub h1: Twist,
    /// The constant absorbing `e(α, β)` and the statement.
    pub d: Gt,
}

impl Verifier {
    /// The verdict `P`, defined when `B ∈ G_2`.
    pub fn verdict(&self, x: &ProofPoints) -> Option<Gt> {
        in_g2(&x.b).then(|| multi_pair([x.a, x.c], [x.b, self.h1]) - self.d)
    }

    /// `Valid_G(x)`: `r·B = O` and `P = 0`.
    pub fn is_valid(&self, x: &ProofPoints) -> bool {
        self.verdict(x).is_some_and(|p| p.is_zero())
    }
}

/// A proof as group elements: the evaluator's input at this layer. `b` is a twist
/// point; whether it lies in `G_2` is part of the function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofPoints {
    /// `A ∈ G_1`.
    pub a: G1,
    /// `B ∈ E'(F_{p^2})`.
    pub b: Twist,
    /// `C ∈ G_1`.
    pub c: G1,
}

/// The garbled program `f~_G`.
#[derive(Clone, Debug)]
pub struct GroupProgram {
    /// The bases `U_t ∈ G_2`.
    pub bases: Vec<Twist>,
    /// The commitments `h_t`.
    pub commits: Vec<[u8; 32]>,
    /// The pad `ct = s ⊕ H(sid, c⃗)`.
    pub ct: Secret,
}

/// The encoding information `ek_G`: the coefficients and keys of the three
/// Argo encodings.
#[derive(Clone, Debug)]
pub struct GroupEncodingInfo {
    /// The binary digits `b_i` of `−k`, least significant first.
    pub a_coeffs: Vec<bool>,
    /// The masks `M_i` on `A`.
    pub a_keys: Vec<G1>,
    /// The coefficient vector `c⃗` shared by `B` and `C`.
    pub coeffs: Vec<bool>,
    /// The keys `K^B_t = k·U_t` on `B`, for the scalar `k` shared across the bases.
    pub b_keys: Vec<Twist>,
    /// The keys `K^C_t` on `C`.
    pub c_keys: Vec<G1>,
}

/// The encoding `x~_G`: the three Argo encodings.
#[derive(Clone, Debug)]
pub struct GroupEncoding {
    /// `⟦A⟧_i = b_i·A + M_i`.
    pub a: Vec<G1>,
    /// `⟦B⟧_t = c_t·B + k·U_t`.
    pub b: Vec<Twist>,
    /// `⟦C⟧_t = c_t·C + K^C_t`.
    pub c: Vec<G1>,
}

/// `c·V`, for a binary coefficient: the identity map or the zero map.
fn phi<P: Clone + Zero>(c: bool, v: &P) -> P {
    if c {
        v.clone()
    } else {
        P::zero()
    }
}

/// The `N` binary digits of `−k`, least significant first.
fn digits_of_neg(k: Fr) -> Vec<bool> {
    let bits = (-k).into_bigint().to_bits_le();
    assert!(bits[N..].iter().all(|&b| !b), "−k has at most n bits");
    bits[..N].to_vec()
}

/// `Σ_i 2^i·points[i]`, by Horner's rule. Used both for `A`'s masks and for its
/// labels, so the same function derives `R` and reconstructs `Q`.
fn weighted_sum<P: AdditiveGroup>(points: &[P]) -> P {
    points
        .iter()
        .rev()
        .fold(P::zero(), |acc, p| acc.double() + *p)
}

/// One byte per coefficient, for hashing into `H(sid, c⃗)`. Both the garbler's
/// `ct` and the evaluator's recovered pad must serialize `c⃗` identically.
fn coeffs_to_bytes(coeffs: &[bool]) -> Vec<u8> {
    coeffs.iter().map(|&c| c as u8).collect()
}

fn rand_nonzero<P: UniformRand + Zero>(rng: &mut impl RngCore) -> P {
    loop {
        let p = P::rand(rng);
        if !p.is_zero() {
            return p;
        }
    }
}

/// The scheme over groups, with its public parameters.
#[derive(Clone, Debug)]
pub struct GroupScheme {
    /// The normalized verifier.
    pub vk: Verifier,
    /// The session identifier, separating the hash domains of different garblings.
    pub sid: Vec<u8>,
}

impl GroupScheme {
    /// The scheme for a verifier and session identifier.
    pub fn new(vk: Verifier, sid: Vec<u8>) -> Self {
        Self { vk, sid }
    }

    /// Open the pad with a recovered coefficient vector.
    fn open(&self, program: &GroupProgram, coeffs: &[bool]) -> Secret {
        xor(&program.ct, &h_key(&self.sid, &coeffs_to_bytes(coeffs)))
    }
}

impl Pgs for GroupScheme {
    type GarblerInput = Secret;
    type Input = ProofPoints;
    type Program = GroupProgram;
    type EncodingInfo = GroupEncodingInfo;
    type Encoding = GroupEncoding;
    type Output = Option<Secret>;

    fn garble<R: RngCore>(&self, rng: &mut R, s: &Secret) -> (GroupProgram, GroupEncodingInfo) {
        let coeffs: Vec<bool> = (0..KAPPA).map(|_| rng.next_u32() & 1 == 1).collect();
        let bases: Vec<Twist> = (0..KAPPA).map(|_| Twist::rand(rng)).collect();
        // Sampling clears the cofactor, and both evaluation branches depend on
        // it: the pairing identity needs bilinearity on G_2, and the subgroup
        // branch needs r·U_t = O. This is independent of whether a base
        // happens to be the identity, which is fine (see the module doc).
        debug_assert!(bases.iter().all(in_g2), "the bases must lie in G_2");
        let c_keys: Vec<G1> = (0..KAPPA).map(|_| G1::rand(rng)).collect();
        let k: Fr = rand_nonzero(rng);
        let a_coeffs = digits_of_neg(k);
        let a_keys: Vec<G1> = (0..N).map(|_| G1::rand(rng)).collect();
        let r_mask = weighted_sum(&a_keys);
        let b_keys: Vec<Twist> = bases.iter().map(|u| *u * k).collect();

        let commits = (0..KAPPA)
            .map(|t| {
                let mut n = multi_pair([r_mask, c_keys[t]], [bases[t], self.vk.h1]);
                if coeffs[t] {
                    n += self.vk.d;
                }
                h_com(&self.sid, t, &n)
            })
            .collect();
        let ct = xor(s, &h_key(&self.sid, &coeffs_to_bytes(&coeffs)));

        (
            GroupProgram { bases, commits, ct },
            GroupEncodingInfo {
                a_coeffs,
                a_keys,
                coeffs,
                b_keys,
                c_keys,
            },
        )
    }

    fn encode(&self, ek: &GroupEncodingInfo, x: &ProofPoints) -> GroupEncoding {
        GroupEncoding {
            a: ek
                .a_coeffs
                .iter()
                .zip(&ek.a_keys)
                .map(|(&c, m)| phi(c, &x.a) + *m)
                .collect(),
            b: ek
                .coeffs
                .iter()
                .zip(&ek.b_keys)
                .map(|(&c, key)| phi(c, &x.b) + *key)
                .collect(),
            c: ek
                .coeffs
                .iter()
                .zip(&ek.c_keys)
                .map(|(&c, key)| phi(c, &x.c) + *key)
                .collect(),
        }
    }

    fn eval(&self, program: &GroupProgram, enc: &GroupEncoding, x: &ProofPoints) -> Option<Secret> {
        // A malformed or truncated program must not panic: the party
        // publishing it is the one that wants disclosure not to happen.
        if enc.a.len() != N
            || enc.b.len() != KAPPA
            || enc.c.len() != KAPPA
            || program.bases.len() != KAPPA
            || program.commits.len() != KAPPA
        {
            return None;
        }

        // Step 1: membership of B in G_2. Off the subgroup, the encoding of B
        // reveals c⃗ through r·⟦B⟧_t = c_t·(r·B).
        let rb = r_times(&x.b);
        if !rb.is_zero() {
            let mut found = Vec::with_capacity(KAPPA);
            for entry in &enc.b {
                let r_entry = r_times(entry);
                if r_entry.is_zero() {
                    found.push(false);
                } else if r_entry == rb {
                    found.push(true);
                } else {
                    return None;
                }
            }
            return Some(self.open(program, &found));
        }

        // Step 2: the verdict in the clear, then the commitments.
        let p = multi_pair([x.a, x.c], [x.b, self.vk.h1]) - self.vk.d;
        if p.is_zero() {
            return None;
        }
        // The pairing is only defined on G_2; an honest encoding of a subgroup
        // point stays in the subgroup, so a label outside it is malformed.
        if !enc.b.iter().all(in_g2) {
            return None;
        }
        let q = weighted_sum(&enc.a);
        let mut found = Vec::with_capacity(KAPPA);
        for t in 0..KAPPA {
            let y = multi_pair([x.a, q, enc.c[t]], [enc.b[t], program.bases[t], self.vk.h1]);
            // The two candidate keys are Y_t itself (c_t = 0) and Y_t − P (c_t = 1).
            // Exactly one should match the commitment; anything else is malformed.
            let matches_zero = h_com(&self.sid, t, &y) == program.commits[t];
            let matches_one = h_com(&self.sid, t, &(y - p)) == program.commits[t];
            match (matches_zero, matches_one) {
                (true, false) => found.push(false),
                (false, true) => found.push(true),
                _ => return None,
            }
        }
        Some(self.open(program, &found))
    }
}
