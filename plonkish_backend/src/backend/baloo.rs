use halo2_curves::bn256::{Bn256, Fr};

use crate::{
    backend::baloo::preprocessor::preprocess,
    pcs::univariate::UnivariateKzg,     
    poly::univariate::UnivariatePolynomial,
};

pub mod preprocessor;
pub mod prover;
pub mod util;
pub mod verifier;
use prover::Prover;
use verifier::Verifier;
type Pcs = UnivariateKzg<Bn256>;

use std::cmp::max;
use rand::thread_rng; 
use rand::seq::SliceRandom; 
use std::collections::HashSet;

use std::time::Instant;


pub fn test_baloo_by_input(table:Vec<Fr>,lookup:Vec<Fr>)->Vec<String> {
    let mut timings: Vec<String> = vec![];

    let m = lookup.len();
        let t = table.len();
        let k=(t as f64).log2();
        let poly_size = max(t, m).next_power_of_two() * 2;
        let d = poly_size - 2;

        // 1. setup and preprocess
        let start = Instant::now();
        let (param, pp, vp) = preprocess(t, m).unwrap();
        assert_eq!(poly_size, 2_usize.pow(pp.k() as u32));
        let duration1 = start.elapsed();
        timings.push(format!("k={k}, setup and preprocess time: {}ms",duration1.as_millis()));
        println!("------------?Setup and preprocess: {}ms-----------",duration1.as_millis());

        // 2. generate proof
        let start = Instant::now();
        let prover = Prover::new(&table, &param, &pp);
        let proof = prover.prove(&lookup);
        let duration2 = start.elapsed();
        timings.push(format!("k={k}, prove time: {}ms", duration2.as_millis()));
        println!("------------prove: {}ms------------", duration2.as_millis());
        println!("proof: {:?}", proof);

        let scalar_0 = Fr::from(0 as u64);
        let scalar_1 = Fr::from(1 as u64);

        // 3.1 prepare for verifier
        // z_h(x) = X^t - 1, [-1, 0, ..., 0, 1], t-1 0s in between
        let z_h_poly_coeffs = vec![scalar_1.neg()]
            .into_iter()
            .chain(vec![scalar_0; t - 1])
            .chain(vec![scalar_1])
            .collect();
        let z_h_poly = UnivariatePolynomial::monomial(z_h_poly_coeffs);
        // [z_h(x)]1
        let z_h_comm_1 = Pcs::commit_monomial(&pp, &z_h_poly.coeffs());
        // t(x)
        let t_poly = UnivariatePolynomial::lagrange(table.clone()).ifft();
        // [t(x)]1
        let t_comm_1 = Pcs::commit_monomial(&pp, &t_poly.coeffs());

        // φ(x)
        let phi_poly = UnivariatePolynomial::lagrange(lookup.clone()).ifft();
        let phi_comm_1 = Pcs::commit_monomial(&pp, &phi_poly.coeffs());
        // todo: cached all [x^s]1, [x^s]2?
        // X^m
        let x_m_exponent_poly = UnivariatePolynomial::monomial(
            vec![scalar_0; m]
                .into_iter()
                .chain(vec![scalar_1])
                .collect(),
        );
        // [X^m]1
        let x_m_exponent_poly_comm_1 =
            Pcs::commit_monomial(&pp, &x_m_exponent_poly.clone().coeffs());

        // X^(d-m+1)
        let coeffs_x_exponent_poly = vec![scalar_0; d - m + 1]
            .into_iter()
            .chain(vec![scalar_1])
            .collect();
        let x_exponent_poly = UnivariatePolynomial::monomial(coeffs_x_exponent_poly);
        // [X^(d-m+1)]2
        let x_exponent_poly_comm_2 = Pcs::commit_monomial_g2(&param, &x_exponent_poly.coeffs());
        println!("x_exponent_poly_comm_2: {:?}", x_exponent_poly_comm_2);

        // X^(d-m+2)
        let coeffs_x_exponent_poly_2 = vec![scalar_0; d - m + 2]
            .into_iter()
            .chain(vec![scalar_1])
            .collect();
        let x_exponent_poly_2 = UnivariatePolynomial::monomial(coeffs_x_exponent_poly_2);
        // [X^(d-m+2)]1
        let x_exponent_poly_2_comm_1 = Pcs::commit_monomial(&pp, &x_exponent_poly_2.coeffs());
        // [X^(d-m+2)]2
        let x_exponent_poly_2_comm_2 = Pcs::commit_monomial_g2(&param, &x_exponent_poly_2.coeffs());

        // 3.2 verifier to verify
        let start = Instant::now();
        let verifier = Verifier::new(&vp);
        verifier.verify(
            &proof,
            &t_comm_1,
            &z_h_comm_1,
            &phi_comm_1,
            &x_m_exponent_poly_comm_1,
            &x_exponent_poly_comm_2,
            &x_exponent_poly_2_comm_1,
            &x_exponent_poly_2_comm_2,
            m,
        );
        let duration3 = start.elapsed();
        timings.push(format!("k={k}, verify time: {}ms", duration3.as_millis()));
        println!("------------verify: {}ms------------", duration3.as_millis());
        println!("Finished to verify: baloo");
        println!("------------------------------------");
        let total_duration=duration1+duration2+duration3;
        timings.push(format!("k={k}, total time: {}ms", total_duration.as_millis()));
        timings
}

fn gengerate_table_and_lookup(k:usize)-> (Vec<Fr>, Vec<Fr>)  {  
    let size = 1 << k; // size = 2^k
    let lookup_size=size;
    let deduplication_size = 1 << (k-2); // caculate deduplication_size of lookup=2^(k-2)
    // （1）generate table
    let table: Vec<usize> = (0..size).collect();
    // （2）generate lookup
    let mut rng = thread_rng();
    let selected_values: HashSet<usize> = table
        .choose_multiple(&mut rng, deduplication_size) 
        .cloned() 
        .collect();
    let mut lookup: Vec<usize> = selected_values
        .iter()
        .cloned() 
        .cycle() 
        .take(lookup_size) 
        .collect();
    lookup.shuffle(&mut rng);

    // （3）print table and lookup 
    println!("Table: {:?}", table);
    println!("Lookup: {:?}", lookup);
    let unique_lookup: HashSet<usize> = lookup.iter().cloned().collect();
    println!("Unique values in lookup: {:?}", unique_lookup);
    println!("Number of unique values in lookup: {}", unique_lookup.len());
    // （4）put table and lookup into Fr
    let table_fr: Vec<Fr> = table.iter().map(|&x| Fr::from(x as u64)).collect();
    let lookup_fr: Vec<Fr> = lookup.iter().map(|&x| Fr::from(x as u64)).collect();
    (table_fr,lookup_fr)
}

pub fn test_baloo_by_k(k:usize)->Vec<String> {
    let mut timings: Vec<String> = vec![];
    let (table,lookup)=gengerate_table_and_lookup(k);
    timings=test_baloo_by_input(table,lookup);
    timings
}


#[cfg(test)]
mod tests {
    use super::*;   
 #[test]
     fn test_baloo() {
        let table_int=[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63];
        let lookup_int=[17, 5, 37, 60, 44, 23, 55, 36, 13, 20, 38, 13, 38, 55, 13, 52, 5, 44, 36, 14, 21, 36, 23, 55, 44, 21, 17, 37, 14, 23, 31, 3, 17, 38, 21, 31, 52, 5, 23, 14, 14, 20, 31, 20, 55, 20, 3, 36, 60, 13, 52, 17, 3, 52, 21, 37, 44, 5, 60, 3, 38, 31, 60, 37]; 
        let table: Vec<Fr> = table_int.iter().map(|&x| Fr::from(x as u64)).collect();
        let lookup: Vec<Fr> = lookup_int.iter().map(|&x| Fr::from(x as u64)).collect();
        test_baloo_by_input(table,lookup);       
    }
}
