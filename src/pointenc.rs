//! Garbling the Argo encoding `c·V + K` of a point from its affine coordinates
//! (Eagen-Lai's MAC, here for a binary coefficient `c ∈ {0, 1}`).
//!
//! The three output coordinates are degree-two polynomials in `(u, v)`, garbled
//! entry-by-entry by [`crate::itpg`]. The template is the same for `c = 0` and
//! `c = 1`, so neither the label count nor a branch choice reveals the
//! coefficient. For mask `K = (a, b)` on `v² = u³ + β`, mixed Jacobian addition
//! reduced mod the curve equation gives
//!
//! ```text
//!   X = 2β − 2bv + a²u + au²
//!   Y = bv² + 3abu² − 3a²uv − (a³ + 4β)v + 3bβ
//!   Z = u − a
//! ```
//!
//! transmitted scaled by `(μ², μ³, μ)`. This is a uniform Jacobian representative
//! of `c·V + K` on every branch but `V = K`, where the triple is identically
//! zero and so gives away the coefficient outright: privacy is statistical
//! (distance `1/r` per entry), not perfect.
//!
//! Both degenerate cases (`Z = 0`, i.e. `V = ±K`) still decode correctly, at no
//! extra cost: `V = K` gives the all-zero triple, decoded as `2K = 2V`; `V = −K`
//! gives `(4b², 8b³, 0)`, a valid Jacobian identity since `b ≠ 0` on an odd-order
//! group. The `V = K` case is what lets a proof chosen after the masks are
//! known (the garbler's own case) evaluate correctly.
//!
//! Binary-only: with more than two coefficients the all-zero triple would no
//! longer identify which one was applied.

use crate::curve::{b1, b2, g1_coords, g1_from_coords, twist_coords, twist_from_coords, Twist, G1};
use crate::itpg::{self, CoordLabels, CoordValues, Cursor, Layout, Monomial, Poly, Shape};
use ark_bn254::{Fq, Fq2};
use ark_ff::{Field, UniformRand, Zero};
use ark_std::rand::RngCore;

/// A curve `v² = u³ + b` over a field, with its point type.
pub trait Curve {
    /// The coordinate field.
    type F: Field;
    /// The point type.
    type Point: Clone + Zero + PartialEq + core::fmt::Debug + core::ops::Add<Output = Self::Point>;
    /// The constant `b`.
    fn b() -> Self::F;
    /// The point with these coordinates, if on the curve.
    fn from_coords(u: Self::F, v: Self::F) -> Option<Self::Point>;
    /// Affine coordinates, or `None` for the point at infinity.
    fn coords(p: &Self::Point) -> Option<(Self::F, Self::F)>;
}

/// `E(F_p)`, the group `G_1`.
pub struct CurveG1;

impl Curve for CurveG1 {
    type F = Fq;
    type Point = G1;
    fn b() -> Fq {
        b1()
    }
    fn from_coords(u: Fq, v: Fq) -> Option<G1> {
        g1_from_coords(u, v)
    }
    fn coords(p: &G1) -> Option<(Fq, Fq)> {
        g1_coords(p)
    }
}

/// The twist `E'(F_{p^2})`.
pub struct CurveTwist;

impl Curve for CurveTwist {
    type F = Fq2;
    type Point = Twist;
    fn b() -> Fq2 {
        b2()
    }
    fn from_coords(u: Fq2, v: Fq2) -> Option<Twist> {
        twist_from_coords(u, v)
    }
    fn coords(p: &Twist) -> Option<(Fq2, Fq2)> {
        twist_coords(p)
    }
}

/// The public monomial templates of `X`, `Y`, `Z`: `(7, 5)` occurrences, twelve
/// in total.
pub fn shapes() -> [Shape; 3] {
    let m = Monomial::new;
    [
        Shape {
            monomials: vec![m(0, 1), m(1, 0), m(2, 0)],
        },
        Shape {
            monomials: vec![m(0, 2), m(2, 0), m(1, 1), m(0, 1)],
        },
        Shape {
            monomials: vec![m(1, 0)],
        },
    ]
}

/// Labels per entry on `u` and on `v`: `(7, 5)`.
pub fn occurrences() -> (usize, usize) {
    shapes().iter().fold((0, 0), |(u, v), s| {
        let (su, sv) = s.occurrences();
        (u + su, v + sv)
    })
}

/// The three coordinate polynomials of one entry, already scaled by `(μ², μ³, μ)`.
///
/// `key` is the mask's affine coordinates, or `None` for the identity.
pub fn entry_polys<F: Field>(c: bool, key: Option<(F, F)>, mu: F, b: F) -> [Poly<F>; 3] {
    let (mu2, mu3) = (mu * mu, mu * mu * mu);
    let z = F::zero();
    let three = F::from(3u64);
    let four = F::from(4u64);
    match (c, key) {
        // The addition law.
        (true, Some((a, bk))) => [
            Poly {
                coeffs: vec![-(bk + bk) * mu2, a * a * mu2, a * mu2],
                constant: (b + b) * mu2,
            },
            Poly {
                coeffs: vec![
                    bk * mu3,
                    three * a * bk * mu3,
                    -three * a * a * mu3,
                    -(a * a * a + four * b) * mu3,
                ],
                constant: three * b * bk * mu3,
            },
            Poly {
                coeffs: vec![mu],
                constant: -a * mu,
            },
        ],
        // An identity mask: the output is V itself, as (u, v, 1).
        (true, None) => [
            Poly {
                coeffs: vec![z, mu2, z],
                constant: z,
            },
            Poly {
                coeffs: vec![z, z, z, mu3],
                constant: z,
            },
            Poly {
                coeffs: vec![z],
                constant: mu,
            },
        ],
        // c = 0: a constant representative of the mask.
        (false, Some((a, bk))) => [
            Poly {
                coeffs: vec![z, z, z],
                constant: a * mu2,
            },
            Poly {
                coeffs: vec![z, z, z, z],
                constant: bk * mu3,
            },
            Poly {
                coeffs: vec![z],
                constant: mu,
            },
        ],
        // c = 0 on an identity mask: the Jacobian representative (1, 1, 0).
        (false, None) => [
            Poly {
                coeffs: vec![z, z, z],
                constant: mu2,
            },
            Poly {
                coeffs: vec![z, z, z, z],
                constant: mu3,
            },
            Poly {
                coeffs: vec![z],
                constant: z,
            },
        ],
    }
}

/// Decode one reconstructed triple. `v_point` is the evaluator's own input
/// point, which the doubling branch returns.
pub fn decode<C: Curve>(triple: [C::F; 3], v_point: &C::Point) -> Option<C::Point> {
    let [x, y, z] = triple;
    if x.is_zero() && y.is_zero() && z.is_zero() {
        // V = K, so the answer is 2K = 2V.
        return Some(v_point.clone() + v_point.clone());
    }
    if !z.is_zero() {
        let zi = z.inverse()?;
        let z2 = zi * zi;
        return C::from_coords(x * z2, y * z2 * zi);
    }
    // Z = 0 represents the identity, provided the triple is a genuine Jacobian
    // representative of it.
    (!x.is_zero() && y * y == x * x * x).then(C::Point::zero)
}

/// The layout of one entry's three polynomials.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EntryLayout {
    /// Layouts of `X`, `Y`, `Z`.
    pub polys: [Layout; 3],
}

/// Lay out `s` entries after the cursor.
pub fn layout_entries(s: usize, cur: &mut Cursor) -> Vec<EntryLayout> {
    let shapes = shapes();
    (0..s)
        .map(|_| EntryLayout {
            polys: [
                itpg::layout(&shapes[0], cur),
                itpg::layout(&shapes[1], cur),
                itpg::layout(&shapes[2], cur),
            ],
        })
        .collect()
}

/// Garble the entries `(c_t·V + K_t)_t`, appending labels to `ek` in layout order.
pub fn garble_entries<C: Curve, R: RngCore>(
    rng: &mut R,
    coeffs: &[bool],
    keys: &[C::Point],
    lays: &[EntryLayout],
    ek: &mut CoordLabels<C::F>,
) {
    assert_eq!(coeffs.len(), keys.len());
    assert_eq!(coeffs.len(), lays.len());
    let shapes = shapes();
    for ((&c, key), lay) in coeffs.iter().zip(keys).zip(lays) {
        let mut mu = C::F::rand(rng);
        while mu.is_zero() {
            mu = C::F::rand(rng);
        }
        let polys = entry_polys(c, C::coords(key), mu, C::b());
        for i in 0..3 {
            itpg::garble(rng, &polys[i], &shapes[i], &lay.polys[i], ek);
        }
    }
}

/// Evaluate the entries from the label values and the public coordinates.
pub fn eval_entries<C: Curve>(
    lays: &[EntryLayout],
    vals: &CoordValues<C::F>,
    u: C::F,
    v: C::F,
) -> Option<Vec<C::Point>> {
    let v_point = C::from_coords(u, v)?;
    lays.iter()
        .map(|lay| {
            let triple = [
                itpg::eval(&lay.polys[0], vals, u, v),
                itpg::eval(&lay.polys[1], vals, u, v),
                itpg::eval(&lay.polys[2], vals, u, v),
            ];
            decode::<C>(triple, &v_point)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::AdditiveGroup;
    use ark_std::UniformRand;

    /// The entry cost: seven on `u`, five on `v`, twelve in total.
    #[test]
    fn entry_costs() {
        assert_eq!(occurrences(), (7, 5));
    }

    /// One entry, garbled and evaluated, for a given coefficient, mask and input.
    fn roundtrip<C: Curve>(
        rng: &mut impl RngCore,
        c: bool,
        key: &C::Point,
        v: &C::Point,
    ) -> Option<C::Point> {
        let mut cur = Cursor::default();
        let lays = layout_entries(1, &mut cur);
        let mut ek = CoordLabels::default();
        garble_entries::<C, _>(rng, &[c], core::slice::from_ref(key), &lays, &mut ek);
        let (u, w) = C::coords(v).expect("the input point is finite");
        let vals = itpg::encode(&ek, u, w);
        eval_entries::<C>(&lays, &vals, u, w).map(|pts| pts[0].clone())
    }

    /// Exactly correct on every mask, including the two cases where the
    /// incomplete addition law degenerates: `K = V` (the all-zero triple) and
    /// `K = -V`. Checked on both `G_1` and the twist, since the decoder is the
    /// same generic code for both, but nothing else confirms it was actually
    /// exercised on `G_2`-shaped points rather than only ever tested on `G_1`.
    fn exact_correctness_on_every_mask<C: Curve>(
        mut rand_point: impl FnMut(&mut dyn RngCore) -> C::Point,
    ) where
        C::Point: core::ops::Neg<Output = C::Point>,
    {
        let mut rng = ark_std::test_rng();
        for _ in 0..8 {
            let v = rand_point(&mut rng);
            let cases: Vec<C::Point> = vec![
                rand_point(&mut rng),
                C::Point::zero(),
                v.clone(),
                -v.clone(),
            ];
            for key in cases {
                for c in [false, true] {
                    let want = if c {
                        v.clone() + key.clone()
                    } else {
                        key.clone()
                    };
                    let got = roundtrip::<C>(&mut rng, c, &key, &v);
                    assert_eq!(got, Some(want), "c = {c}, key = {key:?}");
                }
            }
        }
    }

    #[test]
    fn exact_correctness_on_every_mask_g1() {
        exact_correctness_on_every_mask::<CurveG1>(|rng| G1::rand(rng));
    }

    #[test]
    fn exact_correctness_on_every_mask_twist() {
        exact_correctness_on_every_mask::<CurveTwist>(|rng| Twist::rand(rng));
    }

    /// The two degenerate triples have the shapes the decoder relies on:
    /// all-zero for `V = K`, and `(4b², 8b³, 0)` for `V = −K`.
    #[test]
    fn degenerate_triples() {
        let mut rng = ark_std::test_rng();
        let v = G1::rand(&mut rng);
        let (u, w) = CurveG1::coords(&v).unwrap();

        let [px, py, pz] = entry_polys(true, Some((u, w)), Fq::ONE, b1());
        let shapes = shapes();
        let at = |p: &Poly<Fq>, s: &Shape| p.eval_clear(s, u, w);
        assert_eq!(
            (
                at(&px, &shapes[0]),
                at(&py, &shapes[1]),
                at(&pz, &shapes[2])
            ),
            (Fq::ZERO, Fq::ZERO, Fq::ZERO),
            "V = K gives the all-zero triple"
        );

        let bk = -w;
        let [px, py, pz] = entry_polys(true, Some((u, bk)), Fq::ONE, b1());
        let (x, y, z) = (
            at(&px, &shapes[0]),
            at(&py, &shapes[1]),
            at(&pz, &shapes[2]),
        );
        assert_eq!(x, Fq::from(4u64) * bk * bk);
        assert_eq!(y, Fq::from(8u64) * bk * bk * bk);
        assert!(z.is_zero() && y * y == x * x * x && !x.is_zero());
    }

    /// A uniformly scaled representative carries no more than its point: two
    /// different (coefficient, mask) pairs with the same output are equal in law.
    #[test]
    fn scaling_hides_the_representative() {
        let mut rng = ark_std::test_rng();
        let v = G1::rand(&mut rng);
        let target = G1::rand(&mut rng);
        // c = 1 with mask target − V, and c = 0 with mask target, both encode target.
        let got_one = roundtrip::<CurveG1>(&mut rng, true, &(target - v), &v);
        let got_zero = roundtrip::<CurveG1>(&mut rng, false, &target, &v);
        assert_eq!(got_one, Some(target));
        assert_eq!(got_zero, Some(target));
    }
}
