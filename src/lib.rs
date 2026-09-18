//! Grover: a garbled Groth16 verifier.
//!
//! Accompanies the paper's main-body construction: garbling Groth16 secret
//! disclosure, binary coefficients only.
//!
//! # Reading order
//!
//! 1. [`pgs`] — the interface every layer implements, and composition across a
//!    change of the evaluator's input representation.
//! 2. [`group`] — the scheme over points, the only layer with a new security
//!    proof (the rekeying gadget for a pairing of two evaluator inputs).
//! 3. [`itpg`], then [`pointenc`] — garbling a polynomial, and the coordinate
//!    encoder built from it.
//! 4. [`field`] — the scheme over coordinates, plus the curve checks.
//! 5. [`bits`] — the scheme over bit strings, via the Duty-Free Bits compiler.
//!
//! [`curve`] is BN254 and the hashes, referenced throughout.
//!
//! Notation is additive in all three pairing groups.
//!
//! # Parameters
//!
//! `n = 254`, `κ = 128`, twelve field entries per point,
//! `N_base = 10,758`. [`bits::size_report`] measures the garbled program;
//! [`bits::N_BASE`] and [`bits::aggregate_statistical_bits`] give the entry
//! count and the resulting statistical security.

pub mod bits;
pub mod curve;
pub mod field;
pub mod group;
pub mod itpg;
pub mod pgs;
pub mod pointenc;
pub mod testutil;

pub use bits::{bit_scheme, BitScheme, ProofBits};
pub use curve::Secret;
pub use field::ProofCoords;
pub use group::{ProofPoints, Verifier};
pub use pgs::Pgs;
