use ark_ec::{pairing::Pairing, AffineRepr, Group, CurveGroup};
use ark_ff::PrimeField;
use crypto::sha2::Sha256;
use crypto::digest::Digest;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use crate::{r1cs_to_qap::R1CSToQAP, Groth16};
use std::time::{Duration, Instant};

use super::{PreparedVerifyingKey, Proof, VerifyingKey};

use ark_relations::r1cs::{Result as R1CSResult, SynthesisError};
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use core::ops::{AddAssign, Neg};

/// Prepare the verifying key `vk` for use in proof verification.
pub fn prepare_verifying_key<E: Pairing>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    PreparedVerifyingKey {
        vk: vk.clone(),
        alpha_g1_beta_g2: E::pairing(vk.alpha_g1, vk.beta_g2).0,
        gamma_g2_neg_pc: vk.gamma_g2.into_group().neg().into_affine().into(),
        delta_g2_neg_pc: vk.delta_g2.into_group().neg().into_affine().into(),
    }
}

impl<E: Pairing, QAP: R1CSToQAP> Groth16<E, QAP> {
    /// Prepare proof inputs for use with [`verify_proof_with_prepared_inputs`], wrt the prepared
    /// verification key `pvk` and instance public inputs.
    pub fn prepare_inputs(
        pvk: &PreparedVerifyingKey<E>,
        public_inputs: &[E::ScalarField],
    ) -> R1CSResult<E::G1> {
        if (public_inputs.len() + 1) != pvk.vk.gamma_abc_g1.len() {
            return Err(SynthesisError::MalformedVerifyingKey);
        }

        let mut g_ic = pvk.vk.gamma_abc_g1[0].into_group();
        for (i, b) in public_inputs.iter().zip(pvk.vk.gamma_abc_g1.iter().skip(1)) {
            g_ic.add_assign(&b.mul_bigint(i.into_bigint()));
        }

        Ok(g_ic)
    }

    /// Verify a Groth16 proof `proof` against the prepared verification key `pvk` and prepared public
    /// inputs. This should be preferred over [`verify_proof`] if the instance's public inputs are
    /// known in advance.
    pub fn verify_proof_with_prepared_inputs(
        pvk: &PreparedVerifyingKey<E>,
        proof: &Proof<E>,
        prepared_inputs: &E::G1,
    ) -> R1CSResult<bool> {
        
        //o = hash(A,B)
        let mut s_a = DefaultHasher::new();
        proof.a.into_group().hash(&mut s_a);
        let mut s_b = DefaultHasher::new();
        proof.b.into_group().hash(&mut s_b);
        
        let mut s1 = s_a.finish().to_string(); 
        let s2 = s_b.finish().to_string();
        s1 += &s2;
        let mut hasher = Sha256::new();
        hasher.input_str(&s1);

        let o = E::ScalarField::from_be_bytes_mod_order(&hasher.result_str().as_bytes());
        let o_delta_g1 = pvk.vk.delta_g1.into_group().mul_bigint(&o.into_bigint());



        let qap = E::multi_miller_loop(
            [
                <E::G1Affine as Into<E::G1Prepared>>::into(proof.a),
                o_delta_g1.into_affine().into(),
                prepared_inputs.into_affine().into(),
                proof.c.into(),
            ],
            [
                proof.b.into(),
                proof.b.into(),
                pvk.gamma_g2_neg_pc.clone(),
                pvk.delta_g2_neg_pc.clone(),
            ],
        );

        let test = E::final_exponentiation(qap).ok_or(SynthesisError::UnexpectedIdentity)?;

        //add random oracle
        //let o = hash(proof.a.into(), proof.b.into());
        
        // let o = BigInt::from_bytes_be(Sign::Plus, hasher.result_str()) % p;

        // let o_neg_delta_g1 = pvk.vk.delta_g1.into_group().neg().into_affine().into().mul_bigint(&o.into_bigint());

        

        // Ok(test.0 == newright)

        Ok(test.0 == pvk.alpha_g1_beta_g2)
    }
    

    /// Verify a Groth16 proof `proof` against the prepared verification key `pvk`,
    /// with respect to the instance `public_inputs`.
    pub fn verify_proof(
        pvk: &PreparedVerifyingKey<E>,
        proof: &Proof<E>,
        public_inputs: &[E::ScalarField],
    ) -> R1CSResult<bool> {
        let mut  prepare_time= Duration::new(0, 0);
        let start = Instant::now();
        let prepared_inputs = Self::prepare_inputs(pvk, public_inputs)?;
        prepare_time += start.elapsed();
        //println!("prepare time: {:?} seconds", prepare_time);
        Self::verify_proof_with_prepared_inputs(pvk, proof, &prepared_inputs)
    }
}
