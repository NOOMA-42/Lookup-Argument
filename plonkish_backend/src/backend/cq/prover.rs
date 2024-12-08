use rand::rngs::OsRng;
use num_integer::Roots;
use std::{fmt::Debug, collections::HashSet, ops::Mul, collections::HashMap, collections::hash_map::Entry};
use halo2_curves::bn256::{pairing, Bn256, Fr, G1Affine, G2Affine, G1, G2, Fq};
use crate::{
    poly::{Polynomial, univariate::UnivariatePolynomial},
    backend::baloo::{
      util::{lagrange_interp, multi_pairing},
    },
    backend::cq::{
        util::log_2,
        preprocessor::preprocess,
    },
    pcs::{
        PolynomialCommitmentScheme,
        Additive,
        univariate::{UnivariateKzg, UnivariateKzgParam, UnivariateKzgProverParam, UnivariateKzgVerifierParam, UnivariateKzgCommitment},
    },
    util::{
        arithmetic::{Field, PrimeField, root_of_unity, variable_base_msm, barycentric_weights},
        transcript::{InMemoryTranscript, TranscriptWrite, Keccak256Transcript, FieldTranscript, FieldTranscriptRead, FieldTranscriptWrite, G2TranscriptRead, G2TranscriptWrite},
    }
};

type Pcs = UnivariateKzg<Bn256>;
type Scalar = Fr;

pub struct Prover<'b> {
    table: &'b Vec<Fr>,
    param: &'b UnivariateKzgParam<Bn256>,
    pp: &'b UnivariateKzgProverParam<Bn256>,
    d: usize,
}

impl Prover<'_> {
    pub fn new<'a>(
        table: &'a Vec<Fr>,
        param: &'a UnivariateKzgParam<Bn256>,
        pp: &'a UnivariateKzgProverParam<Bn256>
    ) -> Prover<'a> {
        let d = (1 << pp.k()) - 2;
        Prover { table, param, pp, d }
    }

    pub fn prove(
        &self,
        lookup: &Vec<Fr>,
        q_t_comm_poly_coeffs: &Vec<G1Affine>,
    ) -> Vec<u8>
    {
        let table = self.table.clone();
        let param = self.param.clone();
        let pp = self.pp.clone();
        let d = self.d;

        let m = lookup.len();
        let t = table.len();

        /***********
         Round 1
        ***********/
        /*
        Prover sends commitment of m(x)
        table = [1, 2, 3, 4]
        lookup = [1, 2, 1, 3]
        m = [2, 1, 1, 0]
        */
        
        // initialize transcript
        let mut transcript = Keccak256Transcript::new(());
        // compute m
        let mut duplicates: HashMap<Fr, Fr> = HashMap::new();
        for &value in lookup {
            match duplicates.entry(value) {
                Entry::Occupied(mut entry) => *entry.get_mut() += Fr::from(1),
                Entry::Vacant(entry) => { entry.insert(Fr::from(1)); },
            }
        }

        // get m_values
        let m_values: Vec<Fr> = table.iter()
            .map(|&val| *duplicates.get(&val).unwrap_or(&Fr::from(0)))
            .collect();

        // println!("m_values: {:?}", m_values);
        // m(X)
        let m_poly = UnivariatePolynomial::lagrange(m_values.clone()).ifft();
        // println!("m_poly: {:?}", m_poly);
        // [m(x)]1
        let m_comm_1: UnivariateKzgCommitment<G1Affine> = Pcs::commit_and_write(&pp, &m_poly, &mut transcript).unwrap();
        // println!("m_comm_1: {:?}", m_comm_1);

        let beta: Fr = transcript.squeeze_challenge();

        // π1 = ([m(x)]1)
        let pi_1 = (m_comm_1.clone());

         /***********
         Round 2
        ***********/
        /*
        Prover sends commitment of A(X), Q_A(X), B_0(X), Q_B(X), P(X)
        */

        // 1. commit A(X): Step 1-3 in the paper
        // 1.a. compute A_i values
        //  a_i = m_i / (β + t_i)
        let mut a_values: Vec<Fr> = Vec::new();
        for (i, t_i) in table.iter().enumerate() {
            let a_i = m_values[i] * ((&beta + *t_i).invert().unwrap());
            a_values.push(a_i);
            // sanity check
            assert_eq!(a_i * (&beta + *t_i), m_values[i], "A: not equal");
        }
    
        // println!("A_values: {:?}", a_values);

        // 1.b. compute A(X) from A_i values
        let a_poly = UnivariatePolynomial::lagrange(a_values.clone()).ifft();

        // 1.c. commit A(X)
        let a_comm_1: UnivariateKzgCommitment<G1Affine> = Pcs::commit_and_write(&pp, &a_poly, &mut transcript).unwrap();

        // 2. commit Q_A(X): Step 4 in the paper
        // 2.a. T(X) in lagrange form
        let t_poly = UnivariatePolynomial::lagrange(table.clone()).ifft();

        // 2.b. vanishing polynomial: X^N - 1, N = group_order_N - 1
        // group_order_N = len(table) = t
        // X^N - 1 : [-1, 0, ... , 0, 1] with t-1 0s in between
        let scalar_0 = Fr::from(0);
        let scalar_1 = Fr::from(1);

        let z_v_poly_coeffs = vec![scalar_1.neg()].into_iter().chain(vec![scalar_0; t - 1]).chain(vec![scalar_1]).collect();
        let z_v_poly = UnivariatePolynomial::monomial(z_v_poly_coeffs);
        // println!("z_h_poly: {:?}", z_h_poly);

        // vanishing polynomial: X^n - 1, n = group_order_n - 1
        // group_order_n = len(lookup) = m
        // X^n - 1 : [-1, 0, ... , 0, 1] with m-1 0s in between
        let z_h_poly_coeffs = vec![scalar_1.neg()].into_iter().chain(vec![scalar_0; m - 1]).chain(vec![scalar_1]).collect();
        let z_h_poly = UnivariatePolynomial::monomial(z_h_poly_coeffs);
        // println!("z_h_poly: {:?}", z_h_poly);

        // commit Q_A(X), there are two methods:

        // // ===============Method 1=====================
        // // Method 1: use polynomial to commit Q_A(X)
        // // A(X) * (T(X) + beta)
        // let a_t_poly = &a_poly.poly_mul(t_poly.clone() + beta);
        // // - m(X)
        // let neg_m_poly = &m_poly * (Fr::from(1).neg());
        
        // // Q_A(X), R(X) = (A(X) * (T(X) + beta) - m(X)) / z_v(X)
        // let add_poly = &(a_t_poly + neg_m_poly);
        // let (q_a_poly, r_poly) = add_poly.div_rem(&z_v_poly);
        // assert_eq!(r_poly.evaluate(&scalar_0), scalar_0);

        // // commit Q_A(X)
        // let q_a_comm_1: UnivariateKzgCommitment<G1Affine> = Pcs::commit_and_write(&pp, &q_a_poly, &mut transcript).unwrap();
        // println!("q_a_comm_1: {:?}", q_a_comm_1.clone().to_affine());

        // ===============Method 2====================
        // Here we use method 2: commit Q_A(X) with FK
        // implement FK algorithm to compute q_a_comm_1
        let log_a_values = log_2(a_values.len());
        let a_value_root_of_unity = root_of_unity::<Fr>(log_a_values);
        let roots = (0..a_values.len()).map(|i| a_value_root_of_unity.pow([i as u64])).collect::<Vec<Fr>>();

        let group1_zero = G1Affine { x: Fq::zero(), y: Fq::zero()};

        let mut q_a_comm_1_fk = group1_zero;
        for (i, &a_val) in a_values.iter().enumerate() {
            let mut k_t_comm = group1_zero;
            let mut root = Scalar::one();
            for j in 0..(t as usize) {
                let q_t_coeff = q_t_comm_poly_coeffs[j];
                k_t_comm = (k_t_comm + q_t_coeff * root).into();
                root *= roots[i];
            }
            let scale = roots[i] * (Scalar::from(t as u64).invert().unwrap());
            // Compute Quotient polynomial commitment of T(X)
            let q_t_comm = k_t_comm * scale;
            let a_times_q_t_comm = q_t_comm * a_val;
            q_a_comm_1_fk = (q_a_comm_1_fk + a_times_q_t_comm).into();
        }
        // println!("Commitment of Q_A(X) with FK: {:?} \n", q_a_comm_1_fk);
        transcript.write_commitment(&q_a_comm_1_fk);
    

        // 3. commit B_0(X): Step 5-7 in the paper
        // 3.a. compute B_i values
        //  b_i = 1 / (β + f_i)
        let mut b_values: Vec<Fr> = Vec::new();

        for &f_i in lookup {
            let b_i = scalar_1 * ((&beta + f_i).invert().unwrap());
            b_values.push(b_i);
            // sanity check
            assert_eq!(b_i, scalar_1 * ((&beta + f_i).invert().unwrap()), "B: not equal");
        }

        // println!("B_values: {:?}", b_values);
        let b_poly = UnivariatePolynomial::lagrange(b_values.clone()).ifft();

        // 3.b. compute B_0(X) from B_0_i values, B_0(X) = (B(X) - B(0)) / X
        let x_poly = UnivariatePolynomial::monomial(vec![scalar_0, scalar_1]);
        let b_0_mins_b_0_poly = b_poly.clone() + b_poly.evaluate(&scalar_0).neg();
        let (b_0_poly, r_b_0_poly) = b_0_mins_b_0_poly.div_rem(&x_poly);
        // println!("b_0_poly: {:?}", b_0_poly);
        // println!("r_b_0_poly: {:?}", r_b_0_poly);
        assert_eq!(r_b_0_poly.evaluate(&scalar_0), scalar_0);

        // 3.c. commit B_0(X)
        let b_0_comm_1: UnivariateKzgCommitment<G1Affine> = Pcs::commit_and_write(&pp, &b_0_poly, &mut transcript).unwrap();

        // 4. commit Q_B(X): Step 8-9 in the paper
        // 4.a. f(X) in coefficient form
        let f_poly = UnivariatePolynomial::lagrange(lookup.clone()).ifft();
        // commit f(X)
        let f_comm_1: UnivariateKzgCommitment<G1Affine> = Pcs::commit_and_write(&pp, &f_poly, &mut transcript).unwrap();
        
        // 4.b. compute Q_B(X) in coefficient form
        //  Q_B(X) = (B(X) * (f(X) + beta) - 1) / z_h(X)

        // B(X) * (f(X) + beta)
        let b_f_poly = &b_poly.poly_mul(f_poly.clone() + beta);
        // Q_B(X) = (B(X) * (f(X) + beta) - 1) / z_h(X)
        let (q_b_poly, r_q_b_poly) = (b_f_poly.clone() + (Fr::from(1).neg())).div_rem(&z_h_poly);
        // println!("q_b_poly: {:?}", q_b_poly);
        // println!("r_q_b_poly: {:?}", r_q_b_poly);
        assert_eq!(r_q_b_poly.evaluate(&scalar_0), scalar_0);

        // 4.c. commit Q_B(X): Step 9 in the paper
        let q_b_comm_1: UnivariateKzgCommitment<G1Affine> = Pcs::commit_and_write(&pp, &q_b_poly, &mut transcript).unwrap();

        // 5. commit P(X): Step 10 in the paper
        // N - 1 - (n - 2)
        // N = len(table) = t
        // n = len(lookup) = m
        let x_exponent_order = t - 1 - (m - 2);
        let x_exponent_values_in_coeff = vec![scalar_0; x_exponent_order].into_iter().chain(vec![scalar_1]).collect();
        let x_exponent_poly = UnivariatePolynomial::monomial(x_exponent_values_in_coeff);

        // P(X) = B_0(X) * X^(N - 1 - (n - 2))
        let p_poly = b_0_poly.poly_mul(x_exponent_poly.clone());
        // 5.c. commit P(X)
        let p_comm_1: UnivariateKzgCommitment<G1Affine> = Pcs::commit_and_write(&pp, &p_poly, &mut transcript).unwrap();

        let randomness: Vec<Fr> = transcript.squeeze_challenges(2);
        
        // π2 = ([A(X)]1, [Q_A(X)]1, [B_0(X)]1, [f(X)]1, [Q_B(X)]1, [P(X)]1)
        let pi_2 = (
            a_comm_1.clone(),
            q_a_comm_1_fk.clone(),
            b_0_comm_1.clone(),
            f_comm_1.clone(),
            q_b_comm_1.clone(),
            p_comm_1.clone(),
        );

         /***********
         Round 3
        ***********/
        // 1. V sends random γ,η ∈ F.: Step 1 in the paper
        let gamma = randomness[0];
        let eta = randomness[1];
        // 2. compute b_0_at_gamma: Step 2 in the paper
        let b_0_at_gamma = b_0_poly.evaluate(&gamma);
        transcript.write_field_element(&b_0_at_gamma).unwrap();
        // compute f_at_gamma
        let f_at_gamma = f_poly.evaluate(&gamma);
        transcript.write_field_element(&f_at_gamma).unwrap();
        // 3. compute a_at_0: Step 3 in the paper
        let a_at_0 = a_poly.evaluate(&scalar_0);
        transcript.write_field_element(&a_at_0).unwrap();
        // 4. compute b_at_0: Step 4 in the paper
        // b0 := (N·a0)/n
        let b_at_0 = Fr::from(t as u64) * a_at_0 * (Fr::from(m as u64).invert().unwrap());
        // 5. compute b_at_gamma, and Q_b_at_gamma: Step 5 in the paper
        // Z_H(gamma) = gamma^n - 1
        let z_h_at_gamma = gamma.pow([m as u64]) - Fr::from(1);
        let b_at_gamma = b_0_at_gamma * gamma + b_at_0;
        let q_b_at_gamma = (b_at_gamma * (f_at_gamma + beta) - Fr::from(1)) * (z_h_at_gamma.invert().unwrap());

        // 6. batch KZG check: Step 6 in the paper
        // (a) both P and V compute v
        // v = b_0_at_gamma + f_at_gamma * eta + q_b_at_gamma * eta^2
        let v = Self::rlc(b_0_at_gamma, f_at_gamma, q_b_at_gamma, eta);
        // println!("v: {:?}", v);
        
        // (b) compute commitment: pi_gamma = [h(X)]_1
        //     h_poly = (self.rlc(self.B_0_poly, self.f_poly, self.Q_B_poly) - v) / (self.x_poly - gamma)
        let h_poly_add_term_2 = &f_poly * eta;
        let h_poly_add_term_3 = &q_b_poly * eta.pow([2]);
        let h_poly_add_acum_1 = &b_0_poly + &h_poly_add_term_2;
        let h_poly_add_acum_2 = &h_poly_add_acum_1 + &h_poly_add_term_3;
        let x_poly_minus_gamma = UnivariatePolynomial::monomial(vec![gamma.neg(), scalar_1]);
        let (h_poly, r_h_poly) = (h_poly_add_acum_2 + v.neg()).div_rem(&x_poly_minus_gamma);
        // println!("h_poly: {:?}", h_poly);
        // println!("r_h_poly: {:?}", r_h_poly);
        assert_eq!(r_h_poly.evaluate(&scalar_0), scalar_0);
    
        let pi_gamma: UnivariateKzgCommitment<G1Affine> = Pcs::commit_and_write(&pp, &h_poly, &mut transcript).unwrap();
        // 3.7 commit A_0(X): Step 7 in the paper
        // (a) compute a_0_comm_1
        let (a_0_poly, r_a_0_poly) = (a_poly + a_at_0.neg()).div_rem(&x_poly);      
        // println!("a_0_poly: {:?}", a_0_poly);
        // println!("r_a_0_poly: {:?}", r_a_0_poly);
        assert_eq!(r_a_0_poly.evaluate(&scalar_0), scalar_0);
        let a_0_comm_1: UnivariateKzgCommitment<G1Affine> = Pcs::commit_and_write(&pp, &a_0_poly, &mut transcript).unwrap();    
        // println!("a_0_comm_1: {:?}", a_0_comm_1);

        // π3 = (b_0_at_gamma, f_at_gamma, a_at_0, pi_gamma, a_0_comm_1)
        let pi_3 = (
            b_0_at_gamma.clone(),
            f_at_gamma.clone(),
            a_at_0.clone(),
            pi_gamma.clone(),
            a_0_comm_1.clone(),
        );

        // generate proof from transcript
        transcript.into_proof()
    }

    // random linear combination
    fn rlc(term_1: Fr, term_2: Fr, term_3: Fr, eta: Fr) -> Fr {
        return term_1 + term_2 * eta + term_3 * eta.pow([2]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_curves::bn256::Fr;
    use crate::util::transcript::{FieldTranscriptRead, FieldTranscriptWrite, G2TranscriptRead, G2TranscriptWrite};
    type Pcs = UnivariateKzg<Bn256>;

    #[test]
    fn test_cq() {
        let table = vec![Fr::from(1), Fr::from(2), Fr::from(3), Fr::from(4)];
        let lookup = vec![Fr::from(1), Fr::from(2), Fr::from(1), Fr::from(3)];
        let m = lookup.len();
        let t = table.len();
        // 1. setup
        let (param, pp, vp, q_t_comm_poly_coeffs) = preprocess(t, m, &table).unwrap();

        // println!("param: {:?}\n", param);
        // println!("pp: {:?}", pp);

        // 2. generate proof
        let prover = Prover::new(&table, &param, &pp);
        let proof = prover.prove(&lookup, &q_t_comm_poly_coeffs);
    }
}