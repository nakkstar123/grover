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
use common::{
    points_from_ark, points_with_inputs_from_ark, variable_verifier_from_ark, verifier_from_ark,
};
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

/// A circuit with `N` public inputs, each constrained to the product of two
/// witnesses, so that a proof fixes every input.
#[derive(Clone)]
struct ManyInputs {
    witnesses: Option<Vec<(Fr, Fr)>>,
    count: usize,
}

impl ConstraintSynthesizer<Fr> for ManyInputs {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        for i in 0..self.count {
            let pair = self.witnesses.as_ref().map(|w| w[i]);
            let a = cs.new_witness_variable(|| {
                pair.map(|p| p.0).ok_or(SynthesisError::AssignmentMissing)
            })?;
            let b = cs.new_witness_variable(|| {
                pair.map(|p| p.1).ok_or(SynthesisError::AssignmentMissing)
            })?;
            let c = cs.new_input_variable(|| {
                pair.map(|p| p.0 * p.1)
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        }
        Ok(())
    }
}

/// One garbling, a statement chosen after it: the proof seals for the statement it
/// proves and discloses for any other.
#[test]
fn real_groth16_proof_with_the_statement_left_to_the_evaluator() {
    let mut rng = StdRng::seed_from_u64(11);
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

    let secret: Secret = [0x9E; 16];
    let scheme = bit_scheme(
        variable_verifier_from_ark(&vk, &[None]),
        b"real-g16-variable".to_vec(),
    );
    let (program, ek) = scheme.garble(&mut rng, &secret);

    let points = points_with_inputs_from_ark(&proof, &[c]);
    assert!(scheme.outer.group.vk.is_valid(&points));
    let bits = ProofBits::from_coords(&ProofCoords::from_points(&points).unwrap());
    let enc = scheme.encode(&ek, &bits);
    assert_eq!(scheme.eval(&program, &enc, &bits), None);

    let points = points_with_inputs_from_ark(&proof, &[c + Fr::from(1u64)]);
    assert!(!scheme.outer.group.vk.is_valid(&points));
    let bits = ProofBits::from_coords(&ProofCoords::from_points(&points).unwrap());
    let enc = scheme.encode(&ek, &bits);
    assert_eq!(scheme.eval(&program, &enc, &bits), Some(secret));
}

/// The folding pattern of an SP1 verifier on a real proof: five public inputs, four
/// folded at garbling time, the second left to the evaluator. Whatever is folded or
/// left, the scheme agrees with `ark-groth16`.
#[test]
fn real_groth16_proof_with_part_of_the_statement_folded() {
    let mut rng = StdRng::seed_from_u64(13);
    let shape = ManyInputs {
        witnesses: None,
        count: 5,
    };
    let (pk, vk) = Groth16::<Bn254>::circuit_specific_setup(shape, &mut rng).unwrap();
    let witnesses: Vec<(Fr, Fr)> = (2u64..7)
        .map(|i| (Fr::from(i), Fr::from(i * i + 1)))
        .collect();
    let statement: Vec<Fr> = witnesses.iter().map(|w| w.0 * w.1).collect();
    let proof = Groth16::<Bn254>::prove(
        &pk,
        ManyInputs {
            witnesses: Some(witnesses),
            count: 5,
        },
        &mut rng,
    )
    .unwrap();
    assert!(Groth16::<Bn254>::verify(&vk, &statement, &proof).unwrap());

    let secret: Secret = [0x77; 16];
    let check = |live: &[usize], rng: &mut StdRng| {
        let fixed: Vec<Option<Fr>> = statement
            .iter()
            .enumerate()
            .map(|(i, xi)| (!live.contains(&i)).then_some(*xi))
            .collect();
        let inputs: Vec<Fr> = live.iter().map(|&i| statement[i]).collect();
        let verifier = variable_verifier_from_ark(&vk, &fixed);

        let scheme = bit_scheme(verifier, b"real-g16-folded".to_vec());
        let (program, ek) = scheme.garble(rng, &secret);

        let points = points_with_inputs_from_ark(&proof, &inputs);
        let bits = ProofBits::from_coords(&ProofCoords::from_points(&points).unwrap());
        let enc = scheme.encode(&ek, &bits);
        assert_eq!(scheme.eval(&program, &enc, &bits), None, "live {live:?}");

        for i in 0..inputs.len() {
            let mut wrong = inputs.clone();
            wrong[i] += Fr::from(1u64);
            let points = points_with_inputs_from_ark(&proof, &wrong);
            let bits = ProofBits::from_coords(&ProofCoords::from_points(&points).unwrap());
            let enc = scheme.encode(&ek, &bits);
            assert_eq!(
                scheme.eval(&program, &enc, &bits),
                Some(secret),
                "live {live:?}, wrong {i}"
            );
        }
    };

    check(&[1], &mut rng); // committed_values_digest's position in SP1 v6.
    check(&[0, 2, 4], &mut rng);
    check(&[0, 1, 2, 3, 4], &mut rng);
}
