use halo2_curves::bn256::{Bn256, Fr};

use crate::{
    backend::cq::preprocessor::preprocess,
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


pub fn test_cq_by_input(table:Vec<Fr>,lookup:Vec<Fr>)->Vec<String>  {
    let mut timings: Vec<String> = vec![];
    let m = lookup.len();
    let t = table.len();
    let poly_size = max(t, m).next_power_of_two() * 2;
    let k=(t as f64).log2();

    // 1. setup and preprocess
    let start = Instant::now();
    let (param, pp, vp, q_t_comm_poly_coeffs) = preprocess(t, m, &table).unwrap();
    assert_eq!(poly_size, 2_usize.pow(pp.k() as u32));
    let duration1 = start.elapsed();
    timings.push(format!("k={k}, setup and preprocess time: {}ms",duration1.as_millis()));
    println!("------------?Setup and preprocess: {}ms-----------",duration1.as_millis());

    // 2. generate proof
    let start = Instant::now();
    let prover = Prover::new(&table, &param, &pp);
    let proof = prover.prove(&lookup, &q_t_comm_poly_coeffs);
    let duration2 = start.elapsed();
    timings.push(format!("k={k}, prove time: {}ms", duration2.as_millis()));
    println!("------------prove: {}ms------------", duration2.as_millis());
    println!("proof: {:?}", proof);

    let scalar_0 = Fr::from(0 as u64);
    let scalar_1 = Fr::from(1 as u64);

    // 3 verifier to verify
    // 3.1 prepare for verifier
    // z_v(x) = X^N - 1, [-1, 0, ..., 0, 1], t-1 0s in between
    let z_v_poly_coeffs = vec![scalar_1.neg()].into_iter().chain(vec![scalar_0; t - 1]).chain(vec![scalar_1]).collect();
    let z_v_poly = UnivariatePolynomial::monomial(z_v_poly_coeffs);
    // [z_h(x)]2
    let z_v_comm_2 = Pcs::commit_monomial_g2(&param, &z_v_poly.coeffs());
    // t(x)
    let t_poly = UnivariatePolynomial::lagrange(table.clone()).ifft();
    // [t(x)]2
    let t_comm_2 = Pcs::commit_monomial_g2(&param, &t_poly.coeffs());

    // [X^{N - 1 - (n - 2)}]2
    // x_exponent_poly_comm_2
    let x_exponent_order = t - 1 - (m - 2);
    let x_exponent_values_in_coeff = vec![scalar_0; x_exponent_order].into_iter().chain(vec![scalar_1]).collect();
    let x_exponent_poly = UnivariatePolynomial::monomial(x_exponent_values_in_coeff);
    // commit x_exponent_poly
    let x_exponent_poly_comm_2 = Pcs::commit_monomial_g2(&param, &x_exponent_poly.coeffs());

    // 3.2 verifier to verify
    let start = Instant::now();
    let verifier = Verifier::new(&vp);
    verifier.verify(
        &proof,
        &t_comm_2,
        &z_v_comm_2,
        &x_exponent_poly_comm_2,
        m,
        t
    );
    let duration3 = start.elapsed();
    timings.push(format!("k={k}, verify time: {}ms", duration3.as_millis()));
    println!("------------verify: {}ms------------", duration3.as_millis());
    println!("Finished to verify: cq");
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

pub fn test_cq_by_k(k:usize)->Vec<String> {
    let mut timings: Vec<String> = vec![];
    let (table,lookup)=gengerate_table_and_lookup(k);
    timings=test_cq_by_input(table,lookup);
    timings
}

#[cfg(test)]
mod tests {
    use super::*;   
 #[test]
     fn test_cq() {
        let k=4;
        test_cq_by_k(k);
    }
}