//! `Π_F`: the scheme over fields.
//!
//! The evaluator's input is the proof as six coordinates. On-curve, this is
//! `Π_G ∘_{ι_F} Π_1`, where `Π_1` garbles the three Argo encodings from
//! coordinates ([`crate::pointenc`]). Off-curve, three garbled polynomials
//! `s·g_V(u, v)` (one per proof point) release `s` instead: they vanish on the
//! curves, hiding `s` statistically there, and off-curve the evaluator divides
//! by the public `g_V(u, v)`. Branching is on the public curve equations, not
//! the garbled values, so the output is `s` off-curve even when `s = 0`. The
//! garbled program is `f~_G` itself.
//!
//! Label positions are a fixed public [`FieldLayout`], determined by `n` and
//! `κ` alone.

use crate::curve::{
    b1, b2, fq_to_secret, g1_coords, g1_eq, g1_from_coords, g2_eq, secret_to_fq, twist_coords,
    twist_from_coords, Secret,
};
use crate::group::{
    self, GroupEncoding, GroupEncodingInfo, GroupProgram, GroupScheme, ProofPoints, Verifier,
};
use crate::itpg::{self, CoordLabels, CoordValues, Cursor, Layout, Monomial, Poly, Shape};
use crate::pgs::Pgs;
use crate::pointenc::{self, CurveG1, CurveTwist, EntryLayout};
use ark_bn254::{Fq, Fq2};
use ark_ff::{Field, Zero};
use ark_std::rand::RngCore;

/// A proof as field elements: the evaluator's input at this layer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofCoords {
    /// `(A_u, A_v) ∈ F_p²`.
    pub a: (Fq, Fq),
    /// `(B_u, B_v) ∈ F_{p^2}²`.
    pub b: (Fq2, Fq2),
    /// `(C_u, C_v) ∈ F_p²`.
    pub c: (Fq, Fq),
}

impl ProofCoords {
    /// The map `ι_F`: the points with these coordinates, or `None` if some pair
    /// is off its curve.
    pub fn to_points(&self) -> Option<ProofPoints> {
        Some(ProofPoints {
            a: g1_from_coords(self.a.0, self.a.1)?,
            b: twist_from_coords(self.b.0, self.b.1)?,
            c: g1_from_coords(self.c.0, self.c.1)?,
        })
    }

    /// The coordinates of a proof, or `None` if a point is at infinity.
    pub fn from_points(x: &ProofPoints) -> Option<Self> {
        Some(Self {
            a: g1_coords(&x.a)?,
            b: twist_coords(&x.b)?,
            c: g1_coords(&x.c)?,
        })
    }
}

/// The shape of a curve check `s·(v² − u³ − b)`: monomials `v²` and `u³`, five labels.
pub fn check_shape() -> Shape {
    Shape {
        monomials: vec![Monomial::new(0, 2), Monomial::new(3, 0)],
    }
}

/// The polynomial `s·g(u, v) = s·v² − s·u³ − s·b`.
fn check_poly<F: Field>(s: F, b: F) -> Poly<F> {
    Poly {
        coeffs: vec![s, -s],
        constant: -s * b,
    }
}

/// The layout of one point's labels: its Argo-encoding entries, then its curve check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PointLayout {
    /// Entry layouts.
    pub entries: Vec<EntryLayout>,
    /// Layout of the curve check.
    pub check: Layout,
    /// Total labels on `u` and on `v`.
    pub total: Cursor,
}

impl PointLayout {
    fn new(entries: usize) -> Self {
        let mut cur = Cursor::default();
        let entries = pointenc::layout_entries(entries, &mut cur);
        let check = itpg::layout(&check_shape(), &mut cur);
        Self {
            entries,
            check,
            total: cur,
        }
    }
}

/// The public layout of the field-layer encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldLayout {
    /// Labels on `A`: `n` entries and one check.
    pub a: PointLayout,
    /// Labels on `B`: `κ` entries and one check, over `F_{p^2}`.
    pub b: PointLayout,
    /// Labels on `C`: `κ` entries and one check.
    pub c: PointLayout,
}

impl FieldLayout {
    /// The layout for the scheme's fixed parameters, `n = 254` and `κ = 128`.
    pub fn new() -> Self {
        Self {
            a: PointLayout::new(group::N),
            b: PointLayout::new(group::KAPPA),
            c: PointLayout::new(group::KAPPA),
        }
    }

    /// Entries over the two coordinates of each point: `(S_A, S_B, S_C)`.
    pub fn entry_counts(&self) -> (usize, usize, usize) {
        let n = |p: &PointLayout| p.total.u + p.total.v;
        (n(&self.a), n(&self.b), n(&self.c))
    }

    /// `N_base = S_A + 4·S_B + S_C`, the base-field entries after splitting the
    /// extension-field labels of `B`.
    pub fn base_field_entries(&self) -> usize {
        let (sa, sb, sc) = self.entry_counts();
        sa + 4 * sb + sc
    }
}

impl Default for FieldLayout {
    fn default() -> Self {
        Self::new()
    }
}

/// The encoding information `ek_F`: affine labels on each coordinate.
#[derive(Clone, Debug)]
pub struct FieldEncodingInfo {
    /// Labels on `A_u, A_v`.
    pub a: CoordLabels<Fq>,
    /// Labels on `B_u, B_v`, affine over `F_{p^2}`.
    pub b: CoordLabels<Fq2>,
    /// Labels on `C_u, C_v`.
    pub c: CoordLabels<Fq>,
}

/// The encoding `x~_F`: the label values.
///
/// `Default` gives the empty (wrong-length) encoding used to signal a
/// malformed inner program at the bit layer: [`Pgs::eval`] there cannot return
/// `None` directly (its `Output` is `FieldEncoding`, not `Option<_>`), so it
/// degrades to this value, which this scheme's own length guard then rejects.
#[derive(Clone, Debug, Default)]
pub struct FieldEncoding {
    /// Values on `A`.
    pub a: CoordValues<Fq>,
    /// Values on `B`.
    pub b: CoordValues<Fq2>,
    /// Values on `C`.
    pub c: CoordValues<Fq>,
}

/// The scheme over fields.
#[derive(Clone, Debug)]
pub struct FieldScheme {
    /// The scheme over groups it is built on.
    pub group: GroupScheme,
}

impl FieldScheme {
    /// The scheme for a verifier and session identifier.
    pub fn new(vk: Verifier, sid: Vec<u8>) -> Self {
        Self {
            group: GroupScheme::new(vk, sid),
        }
    }

    /// `Garb_F`, also returning the group encoding information that `Π_1`
    /// garbles. The trait method drops it. It holds the masks and coefficients
    /// of the inner scheme, which a test that supplies an input chosen after the
    /// masks needs.
    pub fn garble_parts<R: RngCore>(
        &self,
        rng: &mut R,
        s: &Secret,
    ) -> (GroupProgram, FieldEncodingInfo, GroupEncodingInfo) {
        let (program, ek_g) = self.group.garble(rng, s);
        let layout = FieldLayout::new();
        let s_fq = secret_to_fq(s);
        let s_fq2 = Fq2::new(s_fq, Fq::zero());

        // Π_1: the three Argo encodings from coordinates, with ek_G as garbler input.
        let mut a = CoordLabels::default();
        pointenc::garble_entries::<CurveG1, _>(
            rng,
            &ek_g.a_coeffs,
            &ek_g.a_keys,
            &layout.a.entries,
            &mut a,
        );
        let mut b = CoordLabels::default();
        pointenc::garble_entries::<CurveTwist, _>(
            rng,
            &ek_g.coeffs,
            &ek_g.b_keys,
            &layout.b.entries,
            &mut b,
        );
        let mut c = CoordLabels::default();
        pointenc::garble_entries::<CurveG1, _>(
            rng,
            &ek_g.coeffs,
            &ek_g.c_keys,
            &layout.c.entries,
            &mut c,
        );

        // Π_γ: the curve checks s·g_V, with s as garbler input.
        let shape = check_shape();
        itpg::garble(
            rng,
            &check_poly(s_fq, b1()),
            &shape,
            &layout.a.check,
            &mut a,
        );
        itpg::garble(
            rng,
            &check_poly(s_fq2, b2()),
            &shape,
            &layout.b.check,
            &mut b,
        );
        itpg::garble(
            rng,
            &check_poly(s_fq, b1()),
            &shape,
            &layout.c.check,
            &mut c,
        );

        (program, FieldEncodingInfo { a, b, c }, ek_g)
    }
}

/// Recover `s` from the check value `z = s·g` and the public nonzero `g`.
fn open_check<F: Field>(z: F, g: F, to_fq: impl Fn(F) -> Option<Fq>) -> Option<Secret> {
    let s = z * g.inverse()?;
    fq_to_secret(to_fq(s)?)
}

impl Pgs for FieldScheme {
    type GarblerInput = Secret;
    type Input = ProofCoords;
    type Program = GroupProgram;
    type EncodingInfo = FieldEncodingInfo;
    type Encoding = FieldEncoding;
    type Output = Option<Secret>;

    fn garble<R: RngCore>(&self, rng: &mut R, s: &Secret) -> (GroupProgram, FieldEncodingInfo) {
        let (program, ek_f, _) = self.garble_parts(rng, s);
        (program, ek_f)
    }

    fn encode(&self, ek: &FieldEncodingInfo, x: &ProofCoords) -> FieldEncoding {
        FieldEncoding {
            a: itpg::encode(&ek.a, x.a.0, x.a.1),
            b: itpg::encode(&ek.b, x.b.0, x.b.1),
            c: itpg::encode(&ek.c, x.c.0, x.c.1),
        }
    }

    fn eval(&self, program: &GroupProgram, enc: &FieldEncoding, x: &ProofCoords) -> Option<Secret> {
        let layout = FieldLayout::new();
        // The party that publishes the program is the one that wants disclosure
        // not to happen, so malformed garbled material must return bottom rather
        // than abort the challenger. The group layer guards its lengths the same
        // way.
        if (enc.a.u.len(), enc.a.v.len()) != (layout.a.total.u, layout.a.total.v)
            || (enc.b.u.len(), enc.b.v.len()) != (layout.b.total.u, layout.b.total.v)
            || (enc.c.u.len(), enc.c.v.len()) != (layout.c.total.u, layout.c.total.v)
        {
            return None;
        }

        // The curve checks. Off a curve, the garbled value z_V = s·g_V(x) divided by
        // the public g_V(x) is s.
        let g_a = g1_eq(x.a.0, x.a.1);
        if !g_a.is_zero() {
            return open_check(itpg::eval(&layout.a.check, &enc.a, x.a.0, x.a.1), g_a, Some);
        }
        let g_b = g2_eq(x.b.0, x.b.1);
        if !g_b.is_zero() {
            let z_b = itpg::eval(&layout.b.check, &enc.b, x.b.0, x.b.1);
            return open_check(z_b, g_b, |s: Fq2| s.c1.is_zero().then_some(s.c0));
        }
        let g_c = g1_eq(x.c.0, x.c.1);
        if !g_c.is_zero() {
            return open_check(itpg::eval(&layout.c.check, &enc.c, x.c.0, x.c.1), g_c, Some);
        }

        // On the curves: Π_G ∘ Π_1. The points exist since the equations vanish.
        let points = x.to_points()?;
        let group_encoding = GroupEncoding {
            a: pointenc::eval_entries::<CurveG1>(&layout.a.entries, &enc.a, x.a.0, x.a.1)?,
            b: pointenc::eval_entries::<CurveTwist>(&layout.b.entries, &enc.b, x.b.0, x.b.1)?,
            c: pointenc::eval_entries::<CurveG1>(&layout.c.entries, &enc.c, x.c.0, x.c.1)?,
        };
        self.group.eval(program, &group_encoding, &points)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The main-body entry count: 10,758 base-field entries.
    #[test]
    fn entry_counts_are_10758() {
        let layout = FieldLayout::new();
        let (sa, sb, sc) = layout.entry_counts();
        assert_eq!((sa, sb, sc), (12 * 254 + 5, 12 * 128 + 5, 12 * 128 + 5));
        assert_eq!((sa, sb, sc), (3053, 1541, 1541));
        assert_eq!(layout.base_field_entries(), 10_758);
        assert_eq!(
            (layout.a.total.u, layout.a.total.v),
            (7 * 254 + 3, 5 * 254 + 2)
        );
    }
}
