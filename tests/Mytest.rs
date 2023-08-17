#![warn(unused)]
#![deny(
    trivial_casts,
    trivial_numeric_casts,
    variant_size_differences,
    stable_features,
    non_shorthand_field_patterns,
    renamed_and_removed_lints,
    private_in_public,
    unsafe_code
)]

use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
// For randomness (during paramgen and proof generation)
use ark_std::rand::{Rng, RngCore, SeedableRng};

// For benchmarking
use std::time::{Duration, Instant};

// Bring in some tools for using pairing-friendly curves
// We're going to use the BLS12-377 pairing-friendly elliptic curve.
use ark_bls12_377::{Bls12_377, Fr};
//use ark_bls12_381::{Bls12_381, Fr};
use ark_ff::Field;
use ark_std::test_rng;

// We'll use these interfaces to construct our circuit.
use ark_relations::{
    lc, ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};

const MIMC_ROUNDS: usize = 322;
const NUM_REPEATITIONS: usize = 6000;

/// This is an implementation of MiMC, specifically a
/// variant named `LongsightF322p3` for BLS12-377.
/// See http://eprint.iacr.org/2016/492 for more
/// information about this construction.
///
/// ```
/// function cubic(x) {
///     x = x^3+x+5
///     return x
/// }
/// ```
fn cubic<F: Field>(mut x: F) -> F {
    
    let mut tmp1 = x;
    tmp1.square_in_place();
    tmp1.mul_assign(&x);
    tmp1.add_assign(&x);
    let five = F::from(5u8);
    tmp1 += five;
    tmp1
}

/// This is our demo circuit for proving knowledge of the
/// preimage of a MiMC hash invocation.
struct CubicDemo<F: Field> {
    x: Option<F>,
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, F: Field> ConstraintSynthesizer<F> for CubicDemo<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        // helper definitions
        let three = F::from(3u8);
        let five = F::from(5u8);
        let nine = F::from(9u8);
        // There will be six variables in the system, in the order governed by adding
        // them to the constraint system (Note that the CS is initialised with
        // `Variable::One` in the first position implicitly).
        // Note also that the all public variables will always be placed before all witnesses
        //
        // Variable::One
        // Variable::Instance(35)
        // Variable::Witness(3) ( == x )
        // Variable::Witness(9) ( == sym_1 )
        // Variable::Witness(27) ( == y )
        // Variable::Witness(30) ( == sym_2 )

        // let one = Variable::One; // public input, implicitly defined
        let mut x_value = self.x;
        let mut x =
            cs.new_witness_variable(|| x_value.ok_or(SynthesisError::AssignmentMissing))?;
        let out = cs.new_input_variable(|| Ok(nine * three + three + five))?; // public input
        //let x = cs.new_witness_variable(|| Ok(three))?; // explicit witness
        let sym_1 = cs.new_witness_variable(|| Ok(nine))?; // intermediate witness variable
        let y = cs.new_witness_variable(|| Ok(nine * three))?; // intermediate witness variable
        let sym_2 = cs.new_witness_variable(|| Ok(nine * three + three))?; // intermediate witness variable

        cs.enforce_constraint(lc!() + x, lc!() + x, lc!() + sym_1)?;
        cs.enforce_constraint(lc!() + sym_1, lc!() + x, lc!() + y)?;
        cs.enforce_constraint(lc!() + y + x, lc!() + Variable::One, lc!() + sym_2)?;
        cs.enforce_constraint(
            lc!() + sym_2 + (five, Variable::One),
            lc!() + Variable::One,
            lc!() + out,
        )?;
        cs.finalize();
        //assert!(cs.is_satisfied().unwrap());
        // let matrices = cs.to_matrices().unwrap();
        // There are four gates(constraints), each generating a row.
        // Resulting matrices:
        // (Note how 2nd & 3rd columns are swapped compared to the online example.
        // This results from an implementation detail of placing all Variable::Instances(_) first.
        //
        // A
        // [0, 0, 1, 0, 0, 0]
        // [0, 0, 0, 1, 0, 0]
        // [0, 0, 1, 0, 1, 0]
        // [5, 0, 0, 0, 0, 1]
        // B
        // [0, 0, 1, 0, 0, 0]
        // [0, 0, 1, 0, 0, 0]
        // [1, 0, 0, 0, 0, 0]
        // [1, 0, 0, 0, 0, 0]
        // C
        // [0, 0, 0, 1, 0, 0]
        // [0, 0, 0, 0, 1, 0]
        // [0, 0, 0, 0, 0, 1]
        // [0, 1, 0, 0, 0, 0]
        Ok(())
    }
}

#[derive(Copy)]
struct DummyCircuit<F: Field> {
    pub a: [Option<F>;NUM_REPEATITIONS],
    pub b: [Option<F>;NUM_REPEATITIONS],
    pub num_variables: usize,
    pub num_constraints: usize,
}

impl<F: Field> Clone for DummyCircuit<F> {
    fn clone(&self) -> Self {
        DummyCircuit {
            a: self.a.clone(),
            b: self.b.clone(),
            num_variables: self.num_variables.clone(),
            num_constraints: self.num_constraints.clone(),
        }
    }
}

impl<F: Field> ConstraintSynthesizer<F> for DummyCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {

        let mut a = cs.new_witness_variable(|| self.a[0].ok_or(SynthesisError::AssignmentMissing))?;
        let mut b = cs.new_witness_variable(|| self.b[0].ok_or(SynthesisError::AssignmentMissing))?;
        let mut c = cs.new_input_variable(|| {
            let a = self.a[0].ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b[0].ok_or(SynthesisError::AssignmentMissing)?;

            Ok(a * b)
        })?;
        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;

        for i in 1..NUM_REPEATITIONS {
        a = cs.new_witness_variable(|| self.a[i].ok_or(SynthesisError::AssignmentMissing))?;
        b = cs.new_witness_variable(|| self.b[i].ok_or(SynthesisError::AssignmentMissing))?;
        c = cs.new_input_variable(|| {
            let a = self.a[i].ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b[i].ok_or(SynthesisError::AssignmentMissing)?;

            Ok(a * b)
        })?;
        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
    }
        // for _ in 0..(self.num_variables - 3) {
        //     let _ = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        // }

        for _ in 0..self.num_constraints - NUM_REPEATITIONS {
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        }

        cs.enforce_constraint(lc!(), lc!(), lc!())?;

        Ok(())
    }
}

#[test]
// fn test_cubic_groth16() {
//     // We're going to use the Groth16 proving system.
//     use ark_groth16::Groth16;

//     // This may not be cryptographically safe, use
//     // `OsRng` (for example) in production software.
//     let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

//     // Generate the MiMC round constants
//     // let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();

//     println!("Creating parameters...");

//     // Create parameters for our circuit
//     let (pk, vk) = {
//         let c = CubicDemo::<Fr> {
//             x: None,
//         };

//         Groth16::<Bls12_377>::setup(c, &mut rng).unwrap()
//     };

//     // Prepare the verification key (for proof verification)
//     let pvk = Groth16::<Bls12_377>::process_vk(&vk).unwrap();

//     println!("Creating proofs...");

//     // Let's benchmark stuff!
//     const SAMPLES: u32 = 50;
//     let mut total_proving = Duration::new(0, 0);
//     let mut total_verifying = Duration::new(0, 0);

//     // Just a place to put the proof data, so we can
//     // benchmark deserialization.
//     // let mut proof_vec = vec![];

//     for _ in 0..SAMPLES {
//         // Generate a random preimage and compute the image
//         // let x = rng.gen();
//         let x = Fr::from(3u8);
//         let image = cubic(x);

//         // proof_vec.truncate(0);

//         let start = Instant::now();
//         {
//             // Create an instance of our circuit (with the
//             // witness)
//             let c = CubicDemo {
//                 x: Some(x),
//             };

//             // Create a groth16 proof with our parameters.
//             let proof = Groth16::<Bls12_377>::prove(&pk, c, &mut rng).unwrap();

//             total_proving += start.elapsed();

//             let start = Instant::now();
//             assert!(
//                 Groth16::<Bls12_377>::verify_with_processed_vk(&pvk, &[image], &proof).unwrap()
//             );
//             total_verifying += start.elapsed();
//             // proof.write(&mut proof_vec).unwrap();
//         }

        

//         // let start = Instant::now();
//         // // let proof = Proof::read(&proof_vec[..]).unwrap();
//         // // Check the proof

//         // total_verifying += start.elapsed();
//     }
//     let proving_avg = total_proving / SAMPLES;
//     let proving_avg =
//         proving_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (proving_avg.as_secs() as f64);

//     let verifying_avg = total_verifying / SAMPLES;
//     let verifying_avg =
//         verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (verifying_avg.as_secs() as f64);

//     println!("Average proving time: {:?} seconds", proving_avg);
//     println!("Average verifying time: {:?} seconds", verifying_avg);
// }


fn test_dummy_groth16() {
    // We're going to use the Groth16 proving system.
    use ark_groth16::Groth16;

    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

    // Generate the MiMC round constants
    // let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();

    println!("Creating parameters...");
    const SAMPLES: u32 = 50;
    let x = Fr::from(3u8);
    let array = [Some(x);NUM_REPEATITIONS];
    // Create parameters for our circuit
    let mut total_crs_generate = Duration::new(0, 0);
    let (pk, vk) = {
        let c = DummyCircuit::<Fr> {
            a: array,
            b: array,
            num_variables: 1000,
            num_constraints: 65536,
        };
        
            // let start = Instant::now();
            // Groth16::<Bls12_377>::generate_random_parameters_with_reduction(c, &mut rng);
            // total_crs_generate += start.elapsed();
        Groth16::<Bls12_377>::setup(c, &mut rng).unwrap()
    };
    // let crs_avg = total_crs_generate;
    // let crs_avg =
    //     crs_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (crs_avg.as_secs() as f64);

    // println!("crs avg generate time: {:?}", crs_avg);

    // Prepare the verification key (for proof verification)
    let pvk = Groth16::<Bls12_377>::process_vk(&vk).unwrap();

    println!("Creating proofs...");

    // Let's benchmark stuff!
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);

    // Just a place to put the proof data, so we can
    // benchmark deserialization.
    // let mut proof_vec = vec![];

    for _ in 0..SAMPLES {
        // Generate a random preimage and compute the image
        //let x = rng.gen();
        //let x = Fr::from(rng);

        // proof_vec.truncate(0);
        let x = Fr::from(3u8);

        let start = Instant::now();
        {
            // Create an instance of our circuit (with the
            // witness)
        
        let array = [Some(x);NUM_REPEATITIONS];
        
            let c = DummyCircuit::<Fr> {
                a: array,
                b: array,
                num_variables: 1000,
                num_constraints: 65536,
            };

            // Create a groth16 proof with our parameters.
            let proof = Groth16::<Bls12_377>::prove(&pk, c, &mut rng).unwrap();

            total_proving += start.elapsed();

            let v = Fr::from(9u8);
            let arraypi = [v;NUM_REPEATITIONS];
            let start = Instant::now();
            assert!(
                Groth16::<Bls12_377>::verify_with_processed_vk(&pvk, &arraypi, &proof).unwrap()
            );
            total_verifying += start.elapsed();
            // proof.write(&mut proof_vec).unwrap();
        }
        

        // let start = Instant::now();
        // // let proof = Proof::read(&proof_vec[..]).unwrap();
        // // Check the proof

        // total_verifying += start.elapsed();
    }
    let proving_avg = total_proving / SAMPLES;
    let proving_avg =
        proving_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (proving_avg.as_secs() as f64);

    let verifying_avg = total_verifying / SAMPLES;
    let verifying_avg =
        verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (verifying_avg.as_secs() as f64);

    // println!("Average proving time: {:?} seconds", proving_avg);
    // println!("Average verifying time: {:?} seconds", verifying_avg);
}