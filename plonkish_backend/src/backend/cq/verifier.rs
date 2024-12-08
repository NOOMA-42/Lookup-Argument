use rand::rngs::OsRng;
use num_integer::Roots;
use std::{fmt::Debug, collections::HashSet, ops::Mul};
use halo2_curves::bn256::{pairing, Bn256, Fr, G1Affine, G2Affine, G1, G2};
use crate::{
    backend::baloo::{
      preprocessor::preprocess, util::{lagrange_interp, multi_pairing}
    }, pcs::{
        univariate::{UnivariateKzg, UnivariateKzgCommitment, UnivariateKzgParam, UnivariateKzgProverParam, UnivariateKzgVerifierParam}, Additive, PolynomialCommitmentScheme
    }, poly::{univariate::UnivariatePolynomial, Polynomial}, util::{
        arithmetic::{barycentric_weights, root_of_unity, variable_base_msm, Field, PrimeField},
        transcript::{FieldTranscript, FieldTranscriptRead, FieldTranscriptWrite, G2TranscriptRead, G2TranscriptWrite, InMemoryTranscript, Keccak256Transcript, TranscriptRead, TranscriptWrite},
    }
};

type Pcs = UnivariateKzg<Bn256>;

pub struct Verifier<'b> {
    vp: &'b UnivariateKzgVerifierParam<Bn256>
}

impl Verifier<'_>
{
    pub fn new<'a>(
        vp: &'a UnivariateKzgVerifierParam<Bn256>
    ) -> Verifier<'a> {
        Verifier { vp }
    }

    pub fn verify(
        &self,
        proof: &Vec<u8>,
        t_comm_2: &UnivariateKzgCommitment<G2Affine>,
        z_v_comm_2: &UnivariateKzgCommitment<G2Affine>,
        x_exponent_poly_comm_2: &UnivariateKzgCommitment<G2Affine>,
        m: usize,
        t: usize
    ) -> bool {
        println!("Start to verify proof");
        let scalar_0 = Fr::from(0 as u64);
        let scalar_1 = Fr::from(1 as u64);
        let vp = self.vp;
        let mut transcript = Keccak256Transcript::from_proof((), proof.as_slice());

        // get commitments
        // read π1 = ([m(x)]1)
        let m_comm_1 = Pcs::read_commitment(&vp, &mut transcript).unwrap();
        println!("m_comm_1: {:?}", m_comm_1);

        let beta: Fr = transcript.squeeze_challenge();

        // read π2 = ([A(X)]1, [Q_A(X)]1, [B_0(X)]1, [f(X)]1, [Q_B(X)]1, [P(X)]1)
        let a_comm_1 = Pcs::read_commitment(&vp, &mut transcript).unwrap();
        println!("a_comm_1: {:?}", a_comm_1);

        let q_a_comm_1_fk: G1Affine = transcript.read_commitment().unwrap();
        println!("q_a_comm_1_fk: {:?}", q_a_comm_1_fk);

        let b_0_comm_1 = Pcs::read_commitment(&vp, &mut transcript).unwrap();
        println!("b_0_comm_1: {:?}", b_0_comm_1);
        
        let f_comm_1 = Pcs::read_commitment(&vp, &mut transcript).unwrap();
        println!("f_comm_1: {:?}", f_comm_1);

        let q_b_comm_1 = Pcs::read_commitment(&vp, &mut transcript).unwrap();
        println!("q_b_comm_1: {:?}", q_b_comm_1);

        let p_comm_1 = Pcs::read_commitment(&vp, &mut transcript).unwrap();
        println!("p_comm_1: {:?}", p_comm_1);

        let randomness: Vec<Fr> = transcript.squeeze_challenges(2);
        let gamma = randomness[0];
        let eta = randomness[1];

        // read π3 = (b_0_at_gamma, f_at_gamma, a_at_0, pi_gamma, a_0_comm_1)
        let b_0_at_gamma: Fr = transcript.read_field_element().unwrap();
        println!("b_0_at_gamma: {:?}", b_0_at_gamma);

        let f_at_gamma: Fr = transcript.read_field_element().unwrap();
        println!("f_at_gamma: {:?}", f_at_gamma);        

        let a_at_0: Fr = transcript.read_field_element().unwrap();
        println!("a_at_0: {:?}", a_at_0);

        let pi_gamma = Pcs::read_commitment(&vp, &mut transcript).unwrap();
        println!("pi_gamma: {:?}", pi_gamma);

        let a_0_comm_1 = Pcs::read_commitment(&vp, &mut transcript).unwrap();
        println!("a_0_comm_1: {:?}", a_0_comm_1);

        /************
        Verification
        ************/
        let g1 = G1::generator();
        let g2 = G2::generator();
        let g1_affine = G1Affine::from(g1);
        let g2_affine = G2Affine::from(g2);
        // Check 1: round 2.11: A encodes the correct values 
        println!("=== Started Check 1: round 2.11: A encodes the correct values ===");
        // comb = ec_lincomb([
        //          (m_comm_1, 1),
        //          (A_comm_1, -beta)
        // ])
        // check
        // e(a, [T(x)]2) = e(q_a, [z_v(x)]2) * e(m - beta * a, [1]2)
        
        let comb: G1Affine = variable_base_msm(
            &[scalar_1, -beta],
            &[m_comm_1.clone().to_affine(), a_comm_1.clone().to_affine()],
        ).into(); 
        let a_check_lhs = pairing(&a_comm_1.clone().to_affine(), &t_comm_2.clone().to_affine());
        let a_check_pairing_g1_terms = vec![q_a_comm_1_fk, comb];
        let a_check_pairing_g2_terms = vec![z_v_comm_2.clone().to_affine(), g2_affine];
        let a_check_rhs = multi_pairing(&a_check_pairing_g1_terms, &a_check_pairing_g2_terms);
        // println!("a_check_lhs: {:?}", a_check_lhs);
        // println!("a_check_rhs: {:?}", a_check_rhs);
        assert_eq!(a_check_lhs, a_check_rhs);
        println!("=== Finished Check 1: round 2.11: A encodes the correct values ===");

        // Check 2: round 2.12: B_0 has the appropriate degree
        // e(b_0, [x^{N-1-(n-2)}]2) == e(p, [1]2)
        println!("=== Started Check 2: round 2.12: B_0 has the appropriate degree ===");
        let b_0_check_lhs = pairing(&b_0_comm_1.clone().to_affine(), &x_exponent_poly_comm_2.clone().to_affine());
        let b_0_check_rhs = pairing(&p_comm_1.clone().to_affine(), &g2_affine);
        // println!("b_0_check_lhs: {:?}", b_0_check_lhs);
        // println!("b_0_check_rhs: {:?}", b_0_check_rhs);
        assert_eq!(b_0_check_lhs, b_0_check_rhs);
        println!("=== Finished Check 2: round 2.12: B_0 has the appropriate degree ===");

        // Check 3: 3.6 (c)
        // c := b_0 + η·cm + η^2·q_b
        // check e(c - [v]1 + gamma * pi_gamma, [1]2) == e(pi_gamma, [x]_2)
        println!("=== Started Check 3: batched KZG check for the correctness of b_0_at_gamma, f_at_gamma, Q_b_at_gamma ===");
        // compute c
        let b_at_0 = Fr::from(t as u64) * a_at_0 * (Fr::from(m as u64).invert().unwrap());
        let z_h_gamma = gamma.pow([m as u64]) - scalar_1;
        let b_gamma = b_0_at_gamma * gamma + b_at_0;
        let q_b_at_gamma = (b_gamma * (f_at_gamma + beta) - scalar_1) * z_h_gamma.invert().unwrap();
        // println!("b_at_0: {:?}", b_at_0);
        // println!("z_h_gamma: {:?}", z_h_gamma);
        // println!("b_gamma: {:?}", b_gamma);
        // println!("q_b_at_gamma: {:?}", q_b_at_gamma);

        // (a) both P and V compute v
        let v = Self::rlc(b_0_at_gamma, f_at_gamma, q_b_at_gamma, eta);
        // println!("v: {:?}", v);

        // v computes c
        // c = ec_lincomb([
        //     (B_0_comm_1, 1),
        //     (f_comm_1, eta),
        //     (Q_B_comm_1, eta * eta)
        // ])
        let c: G1Affine = variable_base_msm(
            &[scalar_1, eta, eta.pow([2])],
            &[b_0_comm_1.clone().to_affine(), f_comm_1.clone().to_affine(), q_b_comm_1.clone().to_affine()],
        ).into(); 
        
        // batched KZG check for the correctness of b_0_at_gamma, f_at_gamma, Q_b_at_gamma
        // comb_batch = ec_lincomb([
        //     (c, 1),
        //     (b.G1, -v),
        //     (pi_gamma, gamma)
        // ])
        let comb_batch: G1Affine = variable_base_msm(
            &[scalar_1, v.neg(), gamma],
            &[c, g1_affine, pi_gamma.clone().to_affine()],
        ).into();
        // check e(c - [v]1 + gamma * pi_gamma, [1]2) == e(pi_gamma, [x]_2)
        let batch_check_lhs = pairing(&comb_batch, &g2_affine);
        let batch_check_rhs = pairing(& pi_gamma.clone().to_affine(), &vp.s_g2());
        // println!("batch_check_lhs: {:?}", batch_check_lhs);
        // println!("batch_check_rhs: {:?}", batch_check_rhs);
        assert_eq!(batch_check_lhs, batch_check_rhs);
        println!("=== Finished Check 3: batched KZG check for the correctness of b_0_at_gamma, f_at_gamma, Q_b_at_gamma ===");

        // Check 4: 3.7 (b)
        // e(a - [a0]1, [1]2) == e(a0, [x]2)
        println!("=== Started Check 4: KZG check for the correctness of a_at_0 ===");
        // a_0_check_comb = ec_lincomb([
        //     # A_comm_1 - a_at_0
        //     (A_comm_1, 1),
        //     (b.G1, -a_at_0)
        // ])
        let a_0_check_comb: G1Affine = variable_base_msm( 
            &[scalar_1, a_at_0.neg()],
            &[a_comm_1.clone().to_affine(), g1_affine],
        ).into();
        let a_0_check_lhs = pairing(&a_0_check_comb, &g2_affine);
        let a_0_check_rhs = pairing(&a_0_comm_1.clone().to_affine(), &vp.s_g2());
        // println!("a_0_check_lhs: {:?}", a_0_check_lhs);
        // println!("a_0_check_rhs: {:?}", a_0_check_rhs);
        assert_eq!(a_0_check_lhs, a_0_check_rhs);
        println!("=== Finished Check 4: KZG check for the correctness of a_at_0 ===");

        println!("Finished to verify proof");
        true
    }

    // random linear combination
    fn rlc(term_1: Fr, term_2: Fr, term_3: Fr, eta: Fr) -> Fr {
        return term_1 + term_2 * eta + term_3 * eta.pow([2]);
    }
}