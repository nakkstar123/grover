//! `Π_bin`: the scheme over bits.
//!
//! The evaluator's input is eight 256-bit blocks: two each for `A` and `C`,
//! four for `B` (the two `F_p` components of each `F_{p^2}` coordinate). The
//! map `ι_bin` reads each block as an integer and reduces it modulo `p`,
//! so an out-of-range block is reduced rather than rejected.
//!
//! `Π_2` garbles the field-layer encoding function, a vector of affine maps
//! `a·x + b`: one Duty-Free Bits instance per `F_p` coordinate. An
//! `F_{p^2}`-affine label `a·(x_0 + η x_1) + b` (`η² = −1`) splits as
//! `(a x_0 + T) + ((aη) x_1 + (b − T))` for uniform `T`, giving two `F_p`-affine
//! labels per component, which the evaluator adds back together.
//!
//! Each DFB instance computes `a·X + b` over the CRT ring `Z_M`. To hide the
//! integer quotient `⌊(a·X + b)/p⌋ < 2^256`, the garbler smudges every offset
//! as `b + μ·p` for uniform `μ ∈ [0, 2^MU_BITS)`; the evaluator reduces the
//! reconstructed integer mod `p`. This hides the quotient to distance `2^-ρ`
//! per label, `ρ = MU_BITS − W` ([`RHO`]); [`BitEncoder::new`] checks the
//! no-wrap bound `p·(2^MU_BITS + 2^W + 1) < M`.
//!
//! The target is 40 bits of statistical security in aggregate: the evaluator
//! sees every label, so what matters is `N_base·2^-ρ`, not the per-label
//! `2^-ρ`. With `N_base = 10,758` that costs about 14 bits, so `ρ = 54`
//! ([`statistical_target_is_met`] checks the aggregate directly).
//!
//! `ι_bin` reads each block least-significant-bit first; a deployed verifier's
//! own serialization convention is a proof-format concern, not this scheme's.

use crate::curve::{block_to_fq, fq_limbs, fq_to_block, p_limbs};
use crate::field::{FieldEncoding, FieldEncodingInfo, FieldScheme, ProofCoords};
use crate::itpg::{Affine, CoordValues};
use crate::pgs::{Compose, Pgs, PublicMap};
use ark_bn254::{Fq, Fq2};
use ark_ff::{BigInt, BigInteger, PrimeField, UniformRand};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::RngCore;
use duty_free_bits::crt::{CrtParams, GarnerDecoder};
use duty_free_bits::pgs as dfb;

/// Bits per block, `w = 256 ≥ ⌈lg p⌉`.
pub const W: usize = 256;
/// Bits of the smudging factor `μ`.
pub const MU_BITS: usize = 310;
/// The statistical smudging parameter `ρ = MU_BITS − W`: the integer quotient of
/// each label is hidden up to statistical distance `2^-ρ`.
pub const RHO: usize = MU_BITS - W;

/// The sampler below masks the top limb of a five-limb `μ`, which assumes the
/// smudging range sits between `2^256` and `2^320`.
const _: () = assert!(
    MU_BITS > W && MU_BITS - W < 64,
    "the top-limb mask assumes 256 < MU_BITS < 320"
);

/// The CRT primes. The Duty-Free Bits crate exports the first 80, whose
/// primorial is `2^552.2` and caps `ρ` at 42. Two more lift it to `2^569.6` and
/// the ceiling to 60, which is what the 40-bit aggregate target needs, and 83
/// would overflow that crate's 576-bit CRT integer.
pub const FIRST_82_PRIMES: [u64; 82] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
    311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
];

/// The base-field entry count of the field layer's encoding,
/// `N_base = 12n + 60κ + 30` (Theorem 11), computed from the same `n`, `κ`
/// constants `group.rs` uses, so the two cannot silently drift apart. The
/// `entry_counts_match_n_base` test cross-checks this against
/// [`crate::field::FieldLayout`], which derives the same total independently
/// from its own per-point layout.
pub const N_BASE: usize = 12 * crate::group::N + 60 * crate::group::KAPPA + 30;

/// The aggregate statistical security, in bits, of projectivizing `N_BASE`
/// labels: the per-label smudging distance `2^-ρ` times the number of labels.
pub fn aggregate_statistical_bits() -> f64 {
    RHO as f64 - (N_BASE as f64).log2()
}

/// The eight blocks, in the order used throughout this module.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Block {
    /// `A_u`.
    AU = 0,
    /// `A_v`.
    AV,
    /// The `F_p` component `c_0` of `B_u`.
    BU0,
    /// The component `c_1` of `B_u`.
    BU1,
    /// `c_0` of `B_v`.
    BV0,
    /// `c_1` of `B_v`.
    BV1,
    /// `C_u`.
    CU,
    /// `C_v`.
    CV,
}

/// Number of blocks.
pub const NUM_BLOCKS: usize = 8;

/// A proof as bits: eight little-endian 256-bit blocks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofBits {
    /// The blocks, indexed by [`Block`].
    pub blocks: [[u8; 32]; NUM_BLOCKS],
}

impl ProofBits {
    /// The canonical blocks of a proof given as coordinates.
    pub fn from_coords(x: &ProofCoords) -> Self {
        Self {
            blocks: [
                fq_to_block(x.a.0),
                fq_to_block(x.a.1),
                fq_to_block(x.b.0.c0),
                fq_to_block(x.b.0.c1),
                fq_to_block(x.b.1.c0),
                fq_to_block(x.b.1.c1),
                fq_to_block(x.c.0),
                fq_to_block(x.c.1),
            ],
        }
    }

    /// The bits of block `i`, least significant first, as `0`/`1` words.
    pub fn bits(&self, i: usize) -> Vec<u64> {
        self.blocks[i]
            .iter()
            .flat_map(|byte| (0..8).map(move |j| ((byte >> j) & 1) as u64))
            .collect()
    }
}

/// The map `ι_bin`: blocks to coordinates, reducing each block modulo `p`.
#[derive(Clone, Copy, Debug, Default)]
pub struct BinToField;

impl PublicMap<ProofBits, ProofCoords> for BinToField {
    fn apply(&self, x: &ProofBits) -> ProofCoords {
        let f = |i: Block| block_to_fq(&x.blocks[i as usize]);
        ProofCoords {
            a: (f(Block::AU), f(Block::AV)),
            b: (
                Fq2::new(f(Block::BU0), f(Block::BU1)),
                Fq2::new(f(Block::BV0), f(Block::BV1)),
            ),
            c: (f(Block::CU), f(Block::CV)),
        }
    }
}

/// `Π_2`: the projectivization of the field-layer encoding function.
#[derive(Clone, Debug)]
pub struct BitEncoder {
    /// The CRT parameters of every DFB instance.
    pub params: CrtParams,
}

impl BitEncoder {
    /// The 82 primes above, with 256-bit inputs. Panics if the smudging range
    /// does not fit below the primorial.
    pub fn new() -> Self {
        let params = CrtParams::from_primes(&FIRST_82_PRIMES, W as u32);
        assert!(
            smudging_fits(&params),
            "p·(2^MU_BITS + 2^W + 1) must be below the CRT modulus M"
        );
        Self { params }
    }
}

/// Whether `p·(2^MU_BITS + 2^W + 1) < M`, which bounds every smudged integer
/// `a·X + b + μ·p` below `M` (exact 640-bit arithmetic).
fn smudging_fits(params: &CrtParams) -> bool {
    type Wide = BigInt<10>;
    let mut factor = Wide::one();
    factor.add_with_carry(&pow2::<10>(MU_BITS));
    factor.add_with_carry(&pow2::<10>(W));
    let mut p = Wide::zero();
    p.0[..4].copy_from_slice(&p_limbs());
    let bound = p.mul_low(&factor);
    let mut m = Wide::zero();
    m.0[..9].copy_from_slice(&params.primorial().0);
    bound < m
}

fn pow2<const N: usize>(k: usize) -> BigInt<N> {
    let mut x = BigInt::<N>::zero();
    x.0[k / 64] = 1u64 << (k % 64);
    x
}

impl Default for BitEncoder {
    fn default() -> Self {
        Self::new()
    }
}

/// The garbled program of `Π_2`: one DFB program per block.
#[derive(Debug)]
pub struct BitProgram {
    /// Indexed by [`Block`].
    pub instances: Vec<dfb::Program>,
}

impl BitProgram {
    /// Ciphertext bits of the DFB programs.
    pub fn program_bits(&self) -> usize {
        self.instances.iter().map(dfb::Program::program_bits).sum()
    }
    /// Bits of the DFB output masks (decoding material).
    pub fn mask_bits(&self) -> usize {
        self.instances.iter().map(dfb::Program::mask_bits).sum()
    }
}

/// The encoding information of `Π_2`: the input-bit masks of each DFB instance.
#[derive(Debug)]
pub struct BitEncodingInfo {
    /// Indexed by [`Block`].
    pub instances: Vec<dfb::EncodingInfo>,
}

/// The projective encoding: one label per input bit.
#[derive(Debug)]
pub struct BitEncoding {
    /// Indexed by [`Block`].
    pub labels: Vec<dfb::InputLabels>,
}

/// `limbs` (little-endian) modulo a small prime.
fn mod_small(limbs: &[u64], p: u64) -> u64 {
    let p = p as u128;
    limbs
        .iter()
        .rev()
        .fold(0u128, |acc, &l| ((acc << 64) | l as u128) % p) as u64
}

/// The affine maps `(a, b)` of `F_p` labels.
fn maps_fq(labels: &[Affine<Fq>]) -> Maps {
    labels.iter().map(|l| (l.a, l.b)).collect()
}

/// The affine maps `(a_j, b_j)` of one DFB instance.
type Maps = Vec<(Fq, Fq)>;

/// Split `F_{p^2}` labels into `F_p` maps on the components `x_0` and `x_1`.
/// Label `j` becomes maps `2j, 2j+1` on each component (the two components of each half).
fn split_fq2<R: RngCore>(rng: &mut R, labels: &[Affine<Fq2>]) -> (Maps, Maps) {
    let mut on_x0 = Vec::with_capacity(2 * labels.len());
    let mut on_x1 = Vec::with_capacity(2 * labels.len());
    for l in labels {
        let t = Fq2::rand(rng);
        let rest = l.b - t;
        // a·x_0 + T, in components.
        on_x0.push((l.a.c0, t.c0));
        on_x0.push((l.a.c1, t.c1));
        // (a·η)·x_1 + (b − T), with a·η = −a_1 + a_0·η since η² = −1.
        on_x1.push((-l.a.c1, rest.c0));
        on_x1.push((l.a.c0, rest.c1));
    }
    (on_x0, on_x1)
}

impl BitEncoder {
    /// Garble one DFB instance for the maps `a_j·x + b_j` over `F_p`, smudging the
    /// offsets, and reducing everything to residues.
    fn garble_instance<R: RngCore>(
        &self,
        rng: &mut R,
        maps: &[(Fq, Fq)],
    ) -> (dfb::Program, dfb::EncodingInfo) {
        let p = p_limbs();
        let a_res: Vec<Vec<u64>> = self
            .params
            .primes
            .iter()
            .map(|&pi| {
                maps.iter()
                    .map(|(a, _)| mod_small(&fq_limbs(*a), pi))
                    .collect()
            })
            .collect();
        let mus: Vec<[u64; 5]> = maps
            .iter()
            .map(|_| {
                let mut mu = [0u64; 5];
                for limb in mu.iter_mut() {
                    *limb = rng.next_u64();
                }
                mu[4] &= (1u64 << RHO) - 1; // ρ low bits of the top limb
                mu
            })
            .collect();
        let b_res: Vec<Vec<u64>> = self
            .params
            .primes
            .iter()
            .map(|&pi| {
                let p_mod = mod_small(&p, pi);
                maps.iter()
                    .zip(&mus)
                    .map(|((_, b), mu)| {
                        (mod_small(&fq_limbs(*b), pi) + mod_small(mu, pi) * p_mod) % pi
                    })
                    .collect()
            })
            .collect();
        let mut seed = [0u8; 32];
        rng.fill_bytes(&mut seed);
        dfb::garble_from_seed(seed, &self.params, &a_res, &b_res)
    }

    /// Evaluate one DFB instance and reduce the reconstructed integers modulo `p`.
    fn eval_instance(
        &self,
        program: &dfb::Program,
        labels: &dfb::InputLabels,
        bits: &[u64],
    ) -> Vec<Fq> {
        let residues = dfb::eval(program, labels, bits);
        let decoder = GarnerDecoder::new(&self.params.primes);
        dfb::by_component(&residues)
            .iter()
            .map(|res| {
                let value = decoder.reconstruct(res);
                let mut bytes = Vec::with_capacity(72);
                for limb in value.0 {
                    bytes.extend_from_slice(&limb.to_le_bytes());
                }
                Fq::from_le_bytes_mod_order(&bytes)
            })
            .collect()
    }
}

impl Pgs for BitEncoder {
    type GarblerInput = FieldEncodingInfo;
    type Input = ProofBits;
    type Program = BitProgram;
    type EncodingInfo = BitEncodingInfo;
    type Encoding = BitEncoding;
    type Output = FieldEncoding;

    fn garble<R: RngCore>(
        &self,
        rng: &mut R,
        ek: &FieldEncodingInfo,
    ) -> (BitProgram, BitEncodingInfo) {
        let (bu0, bu1) = split_fq2(rng, &ek.b.u);
        let (bv0, bv1) = split_fq2(rng, &ek.b.v);
        let per_block: [Maps; NUM_BLOCKS] = [
            maps_fq(&ek.a.u),
            maps_fq(&ek.a.v),
            bu0,
            bu1,
            bv0,
            bv1,
            maps_fq(&ek.c.u),
            maps_fq(&ek.c.v),
        ];
        let mut instances = Vec::with_capacity(NUM_BLOCKS);
        let mut infos = Vec::with_capacity(NUM_BLOCKS);
        for maps in &per_block {
            let (program, info) = self.garble_instance(rng, maps);
            instances.push(program);
            infos.push(info);
        }
        (
            BitProgram { instances },
            BitEncodingInfo { instances: infos },
        )
    }

    fn encode(&self, ek: &BitEncodingInfo, x: &ProofBits) -> BitEncoding {
        BitEncoding {
            labels: (0..NUM_BLOCKS)
                .map(|i| dfb::encode(&ek.instances[i], &x.bits(i)))
                .collect(),
        }
    }

    fn eval(&self, program: &BitProgram, enc: &BitEncoding, x: &ProofBits) -> FieldEncoding {
        // `Output` here is `FieldEncoding`, not `Option<FieldEncoding>`, so a
        // truncated program or encoding cannot be rejected by returning
        // `None`. Degrade to the empty encoding instead: `FieldScheme::eval`'s
        // own length guard rejects it, so the failure still surfaces as `None`
        // one layer up rather than as a panic here.
        if program.instances.len() != NUM_BLOCKS || enc.labels.len() != NUM_BLOCKS {
            return FieldEncoding::default();
        }
        let out: Vec<Vec<Fq>> = (0..NUM_BLOCKS)
            .map(|i| self.eval_instance(&program.instances[i], &enc.labels[i], &x.bits(i)))
            .collect();
        // Reassemble the F_{p^2} values: label j = (half on x_0) + (half on x_1), componentwise.
        let join = |x0: &[Fq], x1: &[Fq]| -> Vec<Fq2> {
            assert_eq!(x0.len(), x1.len());
            (0..x0.len() / 2)
                .map(|j| Fq2::new(x0[2 * j] + x1[2 * j], x0[2 * j + 1] + x1[2 * j + 1]))
                .collect()
        };
        FieldEncoding {
            a: CoordValues {
                u: out[Block::AU as usize].clone(),
                v: out[Block::AV as usize].clone(),
            },
            b: CoordValues {
                u: join(&out[Block::BU0 as usize], &out[Block::BU1 as usize]),
                v: join(&out[Block::BV0 as usize], &out[Block::BV1 as usize]),
            },
            c: CoordValues {
                u: out[Block::CU as usize].clone(),
                v: out[Block::CV as usize].clone(),
            },
        }
    }
}

/// The scheme over bits: `Π_F ∘_{ι_bin} Π_2`.
pub type BitScheme = Compose<FieldScheme, BitEncoder, BinToField>;

/// Build the scheme over bits for a verifier and session identifier.
pub fn bit_scheme(vk: crate::group::Verifier, sid: Vec<u8>) -> BitScheme {
    Compose {
        outer: FieldScheme::new(vk, sid),
        inner: BitEncoder::new(),
        iota: BinToField,
    }
}

/// Size of a garbled program of the scheme over bits, in bits.
///
/// `group_bits` is measured from arkworks' own compressed serialization
/// (`Twist::serialize_compressed`, 64 bytes per base on BN254: a sign bit and
/// an infinity flag on top of the 32-byte-per-coordinate minimum), plus the
/// literal byte lengths of the commitments and the pad. `dfb_ciphertext_bits`
/// and `dfb_output_decoding_bits` come from the Duty-Free Bits crate's own
/// accounting (`Program::program_bits`, `Program::mask_bits`), which has no
/// serialized form to check against. [`SizeReport::total_bits`] is concrete
/// communication accounting, not a serialized byte length.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SizeReport {
    /// `f~_G`: `κ` compressed `G_2` elements, `κ` commitments, one pad.
    /// Measured from the actual serializer, not a hard-coded per-point width.
    pub group_bits: usize,
    /// Duty-Free Bits ciphertexts (the scaling material), excluding output
    /// masks. Named to distinguish it from the masks below, which are also
    /// part of the total: neither is folded into the other.
    pub dfb_ciphertext_bits: usize,
    /// Bits of the Duty-Free Bits output-decoding masks, which the evaluator
    /// subtracts to decode. Kept as an explicit addend of the total, not
    /// absorbed into the outer affine offsets.
    pub dfb_output_decoding_bits: usize,
}

impl SizeReport {
    /// Everything the garbler sends besides the input labels.
    pub fn total_bits(&self) -> usize {
        self.group_bits + self.dfb_ciphertext_bits + self.dfb_output_decoding_bits
    }
}

/// Measures a garbled program of the scheme over bits. See [`SizeReport`].
pub fn size_report(program: &<BitScheme as Pgs>::Program) -> SizeReport {
    let g = &program.0;
    let bases_bytes: usize = g
        .bases
        .iter()
        .map(|u| {
            let mut buf = Vec::new();
            u.serialize_compressed(&mut buf)
                .expect("serializing a group element cannot fail");
            buf.len()
        })
        .sum();
    let commits_bytes = g.commits.len() * core::mem::size_of::<[u8; 32]>();
    let ct_bytes = g.ct.len();
    SizeReport {
        group_bits: (bases_bytes + commits_bytes + ct_bytes) * 8,
        dfb_ciphertext_bits: program.1.program_bits(),
        dfb_output_decoding_bits: program.1.mask_bits(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{BigInteger, UniformRand};

    #[test]
    fn mod_small_matches_field_reduction() {
        let mut rng = ark_std::test_rng();
        for _ in 0..10 {
            let x = Fq::rand(&mut rng);
            for &p in &FIRST_82_PRIMES[..10] {
                let want = (x
                    .into_bigint()
                    .to_bytes_le()
                    .iter()
                    .rev()
                    .fold(0u128, |acc, &b| ((acc << 8) | b as u128) % p as u128))
                    as u64;
                assert_eq!(mod_small(&fq_limbs(x), p), want);
            }
        }
    }

    /// The aggregate statistical target the crate claims is actually met, and by
    /// the parameter the code uses rather than by the per-label figure.
    #[test]
    fn statistical_target_is_met() {
        assert_eq!(RHO, 54);
        let bits = aggregate_statistical_bits();
        assert!(bits >= 40.0, "{bits:.2} bits, below the 40-bit target");
        // The per-label figure alone would mislead: N_base costs about 14 bits.
        assert!(bits < RHO as f64 - 13.0);
    }

    /// The no-wrap bound holds at the chosen `μ` width, and the ring's own
    /// ceiling is `ρ = 60`, so the 40-bit target is met with room rather than by
    /// exhausting the modulus.
    #[test]
    fn smudging_fits_with_headroom() {
        let params = CrtParams::from_primes(&FIRST_82_PRIMES, W as u32);
        assert!(smudging_fits(&params));

        let fits = |mu_bits: usize| {
            let mut factor = Wide::one();
            factor.add_with_carry(&pow2::<10>(mu_bits));
            factor.add_with_carry(&pow2::<10>(W));
            let mut p = Wide::zero();
            p.0[..4].copy_from_slice(&p_limbs());
            let mut m = Wide::zero();
            m.0[..9].copy_from_slice(&params.primorial().0);
            p.mul_low(&factor) < m
        };
        assert!(fits(W + 60), "the ring admits rho = 60");
        assert!(!fits(W + 61), "and no more");
    }

    // MU_BITS is a choice within the ring's headroom, not the ceiling itself.
    const _: () = assert!(MU_BITS < W + 60);

    type Wide = BigInt<10>;

    #[test]
    fn split_fq2_halves_sum_to_the_label() {
        let mut rng = ark_std::test_rng();
        let labels: Vec<Affine<Fq2>> = (0..4)
            .map(|_| Affine {
                a: Fq2::rand(&mut rng),
                b: Fq2::rand(&mut rng),
            })
            .collect();
        let (on_x0, on_x1) = split_fq2(&mut rng, &labels);
        let x = Fq2::rand(&mut rng);
        for (j, l) in labels.iter().enumerate() {
            let h0 = |k: usize| on_x0[2 * j + k].0 * x.c0 + on_x0[2 * j + k].1;
            let h1 = |k: usize| on_x1[2 * j + k].0 * x.c1 + on_x1[2 * j + k].1;
            let got = Fq2::new(h0(0) + h1(0), h0(1) + h1(1));
            assert_eq!(got, l.at(x));
        }
    }
}
