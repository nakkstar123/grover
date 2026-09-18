//! Partial garbling schemes and their composition across a change of the
//! evaluator's input representation.
//!
//! A partial garbling scheme for `f(x, y)` lets a garbler who holds `y` produce a
//! program and encoding information, an encoder who holds the encoding
//! information turn the evaluator's public input `x` into an encoding, and the
//! evaluator compute `f(x, y)` from the program, the encoding, and `x`. Privacy
//! says the evaluator learns nothing about `y` beyond `f(x, y)`.
//!
//! The scheme object carries the public parameters (verification key, session
//! identifier, CRT parameters); the three methods are the algorithms.

use ark_std::rand::RngCore;

/// A partial garbling scheme for a function `f: Input × GarblerInput → Output`.
pub trait Pgs {
    /// The garbler's private input `y`.
    type GarblerInput;
    /// The evaluator's public input `x`.
    type Input;
    /// The garbled program `f~`.
    type Program;
    /// The encoding information `ek`, kept by the garbler.
    type EncodingInfo;
    /// The encoding `x~` of the evaluator's input.
    type Encoding;
    /// The function's output.
    type Output;

    /// `Garb(1^λ, y) → (f~, ek)`.
    fn garble<R: RngCore>(
        &self,
        rng: &mut R,
        y: &Self::GarblerInput,
    ) -> (Self::Program, Self::EncodingInfo);

    /// `Enc(ek, x) → x~`.
    fn encode(&self, ek: &Self::EncodingInfo, x: &Self::Input) -> Self::Encoding;

    /// `Eval(f~, x~) → f(x, y)`. The evaluator's input is public, so it is
    /// passed alongside the encoding.
    fn eval(
        &self,
        program: &Self::Program,
        encoding: &Self::Encoding,
        x: &Self::Input,
    ) -> Self::Output;
}

/// A public map `ι: A → B` between evaluator input domains.
pub trait PublicMap<A, B> {
    /// Apply the map.
    fn apply(&self, x: &A) -> B;
}

/// `Π_f ∘_ι Π_g`: the outer scheme `Π_f` for `f`, and an inner scheme
/// `Π_g` for the outer scheme's encoding function `(x', ek_f) ↦ Enc_f(ek_f, ι(x'))`.
///
/// The composite garbles `f ∘ ι`. Its program is the pair of programs, its
/// encoding information and encoding are those of the inner scheme, and its
/// evaluation runs the inner evaluator and then the outer one on the result.
pub struct Compose<F, G, I> {
    /// The outer scheme `Π_f`.
    pub outer: F,
    /// The inner scheme `Π_g`, garbling the outer encoding function.
    pub inner: G,
    /// The public map `ι` from the inner input domain to the outer one.
    pub iota: I,
}

impl<F, G, I> Pgs for Compose<F, G, I>
where
    F: Pgs,
    G: Pgs<GarblerInput = F::EncodingInfo, Output = F::Encoding>,
    I: PublicMap<G::Input, F::Input>,
{
    type GarblerInput = F::GarblerInput;
    type Input = G::Input;
    type Program = (F::Program, G::Program);
    type EncodingInfo = G::EncodingInfo;
    type Encoding = G::Encoding;
    type Output = F::Output;

    fn garble<R: RngCore>(
        &self,
        rng: &mut R,
        y: &Self::GarblerInput,
    ) -> (Self::Program, Self::EncodingInfo) {
        let (f, ek_f) = self.outer.garble(rng, y);
        let (g, ek_g) = self.inner.garble(rng, &ek_f);
        ((f, g), ek_g)
    }

    fn encode(&self, ek: &Self::EncodingInfo, x: &Self::Input) -> Self::Encoding {
        self.inner.encode(ek, x)
    }

    fn eval(
        &self,
        program: &Self::Program,
        encoding: &Self::Encoding,
        x: &Self::Input,
    ) -> Self::Output {
        let outer_encoding = self.inner.eval(&program.1, encoding, x);
        self.outer
            .eval(&program.0, &outer_encoding, &self.iota.apply(x))
    }
}
