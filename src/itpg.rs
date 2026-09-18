//! The information-theoretic partial garbling of a polynomial in two
//! coordinates `u, v` (Lemma 3, sum of monomials). Each monomial is a chain of
//! affine labels, one per variable occurrence, telescoping to the monomial's
//! value plus an offset; the offsets across monomials sum to the constant
//! term. Perfectly private: the labels are a uniform additive sharing of the
//! output.
//!
//! Label positions are a public [`Layout`], determined by the polynomial's
//! [`Shape`] alone. Only the label coefficients are private.

use ark_ff::Field;
use ark_std::rand::RngCore;

/// One of the two coordinates of a point.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Var {
    /// The `u` coordinate.
    U,
    /// The `v` coordinate.
    V,
}

/// The monomial `u^du · v^dv`, of degree at least one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Monomial {
    /// Degree in `u`.
    pub du: u8,
    /// Degree in `v`.
    pub dv: u8,
}

impl Monomial {
    /// `u^du · v^dv`.
    pub const fn new(du: u8, dv: u8) -> Self {
        Self { du, dv }
    }
    /// Total degree, which is the number of labels the monomial costs.
    pub fn degree(&self) -> usize {
        self.du as usize + self.dv as usize
    }
    /// The variables in chain order: the `u` occurrences, then the `v` occurrences.
    pub fn vars(&self) -> impl Iterator<Item = Var> {
        core::iter::repeat_n(Var::U, self.du as usize)
            .chain(core::iter::repeat_n(Var::V, self.dv as usize))
    }
}

/// The public shape of a polynomial: its non-constant monomials in a fixed order.
/// A constant term is always present and needs no entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Shape {
    /// The monomials, in the order their chains are laid out.
    pub monomials: Vec<Monomial>,
}

impl Shape {
    /// Total number of labels on `u` and on `v`.
    pub fn occurrences(&self) -> (usize, usize) {
        self.monomials
            .iter()
            .fold((0, 0), |(u, v), m| (u + m.du as usize, v + m.dv as usize))
    }
}

/// A polynomial matching a [`Shape`]: one coefficient per monomial, and a constant.
#[derive(Clone, Debug)]
pub struct Poly<F> {
    /// Coefficients, in the shape's order.
    pub coeffs: Vec<F>,
    /// The constant term.
    pub constant: F,
}

impl<F: Field> Poly<F> {
    /// Evaluate in the clear (for tests and for the correctness argument).
    pub fn eval_clear(&self, shape: &Shape, u: F, v: F) -> F {
        let mut acc = self.constant;
        for (m, c) in shape.monomials.iter().zip(&self.coeffs) {
            acc += *c * u.pow([m.du as u64]) * v.pow([m.dv as u64]);
        }
        acc
    }
}

/// An affine label `a·x + b` on one coordinate: one entry of the affine encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Affine<F> {
    /// The coefficient.
    pub a: F,
    /// The offset.
    pub b: F,
}

impl<F: Field> Affine<F> {
    /// The label's value on coordinate value `x`.
    pub fn at(&self, x: F) -> F {
        self.a * x + self.b
    }
}

/// Encoding information for the two coordinates of one point: the labels on `u`
/// and on `v`, in layout order. This is the garbler's `(a, b)` data.
#[derive(Clone, Debug, Default)]
pub struct CoordLabels<F> {
    /// Labels on `u`.
    pub u: Vec<Affine<F>>,
    /// Labels on `v`.
    pub v: Vec<Affine<F>>,
}

/// The encoding of one point's coordinates: the label values, in layout order.
#[derive(Clone, Debug, Default)]
pub struct CoordValues<F> {
    /// Values of the labels on `u`.
    pub u: Vec<F>,
    /// Values of the labels on `v`.
    pub v: Vec<F>,
}

impl<F: Field> CoordValues<F> {
    fn get(&self, var: Var, i: usize) -> F {
        match var {
            Var::U => self.u[i],
            Var::V => self.v[i],
        }
    }
}

/// Where a polynomial's labels sit: one chain per monomial, each a list of
/// `(coordinate, index into that coordinate's label vector)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    /// One chain per monomial, in the shape's order.
    pub chains: Vec<Vec<(Var, usize)>>,
}

/// A cursor over the label positions already allocated on each coordinate.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Cursor {
    /// Labels allocated on `u` so far.
    pub u: usize,
    /// Labels allocated on `v` so far.
    pub v: usize,
}

impl Cursor {
    fn next(&mut self, var: Var) -> usize {
        let slot = match var {
            Var::U => &mut self.u,
            Var::V => &mut self.v,
        };
        let i = *slot;
        *slot += 1;
        i
    }
}

/// Lay out the labels of a polynomial of the given shape after the cursor.
pub fn layout(shape: &Shape, cur: &mut Cursor) -> Layout {
    let chains = shape
        .monomials
        .iter()
        .map(|m| m.vars().map(|var| (var, cur.next(var))).collect())
        .collect();
    Layout { chains }
}

/// Garble `poly` (of shape `shape`, laid out at `lay`), appending its labels to `ek`.
///
/// The labels must be appended in layout order, so the caller garbles polynomials
/// in the order it laid them out; the positions are checked.
pub fn garble<F: Field, R: RngCore>(
    rng: &mut R,
    poly: &Poly<F>,
    shape: &Shape,
    lay: &Layout,
    ek: &mut CoordLabels<F>,
) {
    let m = shape.monomials.len();
    assert!(
        m >= 1,
        "a polynomial with no variable monomial cannot hide its constant"
    );
    assert_eq!(poly.coeffs.len(), m);
    assert_eq!(lay.chains.len(), m);

    // Offsets r_j with Σ r_j = constant.
    let mut offsets: Vec<F> = (0..m - 1).map(|_| F::rand(rng)).collect();
    let partial: F = offsets.iter().copied().sum();
    offsets.push(poly.constant - partial);

    for (j, mono) in shape.monomials.iter().enumerate() {
        let d = mono.degree();
        let chain = &lay.chains[j];
        assert_eq!(chain.len(), d);
        let mut prev_rho = F::zero();
        for (k, &(var, idx)) in chain.iter().enumerate() {
            let a = if k == 0 { poly.coeffs[j] } else { -prev_rho };
            let b = if k == d - 1 { offsets[j] } else { F::rand(rng) };
            prev_rho = b;
            let list = match var {
                Var::U => &mut ek.u,
                Var::V => &mut ek.v,
            };
            assert_eq!(list.len(), idx, "labels must be appended in layout order");
            list.push(Affine { a, b });
        }
    }
}

/// The encoding of coordinates `(u, v)`: every label's value.
pub fn encode<F: Field>(ek: &CoordLabels<F>, u: F, v: F) -> CoordValues<F> {
    CoordValues {
        u: ek.u.iter().map(|l| l.at(u)).collect(),
        v: ek.v.iter().map(|l| l.at(v)).collect(),
    }
}

/// Evaluate a garbled polynomial from the label values and the public coordinates.
pub fn eval<F: Field>(lay: &Layout, vals: &CoordValues<F>, u: F, v: F) -> F {
    let x = |var: Var| match var {
        Var::U => u,
        Var::V => v,
    };
    lay.chains
        .iter()
        .map(|chain| {
            let mut acc = vals.get(chain[0].0, chain[0].1);
            for &(var, idx) in &chain[1..] {
                acc = acc * x(var) + vals.get(var, idx);
            }
            acc
        })
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{Fq, Fq2};
    use ark_ff::UniformRand;

    fn check<F: Field>(rng: &mut impl RngCore) {
        let shape = Shape {
            monomials: vec![
                Monomial::new(0, 1),
                Monomial::new(1, 0),
                Monomial::new(2, 0),
                Monomial::new(0, 2),
                Monomial::new(1, 1),
                Monomial::new(3, 0),
            ],
        };
        let poly = Poly {
            coeffs: (0..6).map(|_| F::rand(rng)).collect(),
            constant: F::rand(rng),
        };
        let mut cur = Cursor::default();
        let lay = layout(&shape, &mut cur);
        let (nu, nv) = shape.occurrences();
        assert_eq!((cur.u, cur.v), (nu, nv));
        assert_eq!((nu, nv), (1 + 2 + 1 + 3, 1 + 2 + 1));

        let mut ek = CoordLabels::default();
        garble(rng, &poly, &shape, &lay, &mut ek);
        assert_eq!(ek.u.len(), nu);
        assert_eq!(ek.v.len(), nv);

        for _ in 0..8 {
            let (u, v) = (F::rand(rng), F::rand(rng));
            let vals = encode(&ek, u, v);
            assert_eq!(eval(&lay, &vals, u, v), poly.eval_clear(&shape, u, v));
        }
    }

    #[test]
    fn garbled_polynomial_evaluates_correctly() {
        let mut rng = ark_std::test_rng();
        check::<Fq>(&mut rng);
        check::<Fq2>(&mut rng);
    }

    /// Two polynomials of the same shape produce label vectors of the same
    /// length and layout, whatever their coefficients (including zero).
    #[test]
    fn shape_determines_layout() {
        let mut rng = ark_std::test_rng();
        let shape = Shape {
            monomials: vec![Monomial::new(0, 1), Monomial::new(2, 0)],
        };
        let mut c1 = Cursor::default();
        let mut c2 = Cursor::default();
        let l1 = layout(&shape, &mut c1);
        let l2 = layout(&shape, &mut c2);
        assert_eq!(l1, l2);
        let zero = Poly {
            coeffs: vec![Fq::from(0u64), Fq::from(0u64)],
            constant: Fq::rand(&mut rng),
        };
        let mut ek = CoordLabels::default();
        garble(&mut rng, &zero, &shape, &l1, &mut ek);
        assert_eq!((ek.u.len(), ek.v.len()), (2, 1));
    }
}
