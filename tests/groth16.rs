//! The scheme over bits on a genuine `ark-groth16` proof: the proof's canonical
//! blocks seal for the statement it proves and disclose for any other statement.

mod common;

use ark_bn254::{Bn254, Fr};
use ark_groth16::Groth16;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};
use ark_snark::SNARK;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use common::{points_from_ark, verifier_from_ark};
use grover::bits::ProofBits;
use grover::field::ProofCoords;
use grover::pgs::Pgs;
use grover::{bit_scheme, Secret};

/// `a · b = c` with public `c`.
#[derive(Clone)]
struct MulCircuit {
    a: Option<Fr>,
    b: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for MulCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
            Ok(a * b)
        })?;
        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        Ok(())
    }
}

#[test]
fn real_groth16_proof_seals_for_its_statement_and_discloses_otherwise() {
    let mut rng = StdRng::seed_from_u64(7);
    let (pk, vk) =
        Groth16::<Bn254>::circuit_specific_setup(MulCircuit { a: None, b: None }, &mut rng)
            .unwrap();
    let (a, b) = (Fr::from(3u64), Fr::from(11u64));
    let c = a * b;
    let proof = Groth16::<Bn254>::prove(
        &pk,
        MulCircuit {
            a: Some(a),
            b: Some(b),
        },
        &mut rng,
    )
    .unwrap();
    assert!(Groth16::<Bn254>::verify(&vk, &[c], &proof).unwrap());

    let points = points_from_ark(&proof);
    let bits = ProofBits::from_coords(&ProofCoords::from_points(&points).unwrap());
    let secret: Secret = [0x9E; 16];

    // The statement the proof is for: seals.
    let scheme = bit_scheme(verifier_from_ark(&vk, &[c]), b"real-g16".to_vec());
    assert!(scheme.outer.group.vk.is_valid(&points));
    let (program, ek) = scheme.garble(&mut rng, &secret);
    let enc = scheme.encode(&ek, &bits);
    assert_eq!(scheme.eval(&program, &enc, &bits), None);

    // A different statement: the same proof is invalid and discloses.
    let scheme = bit_scheme(
        verifier_from_ark(&vk, &[c + Fr::from(1u64)]),
        b"real-g16".to_vec(),
    );
    assert!(!scheme.outer.group.vk.is_valid(&points));
    let (program, ek) = scheme.garble(&mut rng, &secret);
    let enc = scheme.encode(&ek, &bits);
    assert_eq!(scheme.eval(&program, &enc, &bits), Some(secret));
}
