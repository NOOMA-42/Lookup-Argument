use rand::rngs::OsRng;
use std::{cmp::max, iter};
use crate::{
    pcs::PolynomialCommitmentScheme,
    Error,
    backend::cq::util::{ec_fft, ec_ifft, fft, ifft}
};
use halo2_curves::bn256::{pairing, Bn256, Fr, G1Affine, G2Affine, G1, G2, Fq};
use crate::pcs::univariate::{UnivariateKzg, UnivariateKzgParam, UnivariateKzgProverParam, UnivariateKzgVerifierParam};

type Pcs = UnivariateKzg<Bn256>;
type Scalar = Fr;

pub fn preprocess(
    t: usize,
    m: usize,
    table: & Vec<Fr>
) -> Result<
    (
        UnivariateKzgParam<Bn256>,
        UnivariateKzgProverParam<Bn256>,
        UnivariateKzgVerifierParam<Bn256>,
        Vec<G1Affine>, 
    ), 
    Error>
{
    let mut rng = OsRng;
    let poly_size = max(t.next_power_of_two() * 2, m.next_power_of_two() * 2);
    let param = Pcs::setup(poly_size, 1, &mut rng).unwrap();
    let (pp, vp) = Pcs::trim(&param, poly_size, 1).unwrap();
    let mut powers_of_x = pp.monomial_g1()[..t].to_vec();
    let q_t_comm_poly_coeffs = precompute_with_fk(table, &mut powers_of_x);
    Ok((param, pp, vp, q_t_comm_poly_coeffs))
}

fn fk(coeffs: &mut Vec<Fr>, powers_of_x: &mut Vec<G1Affine>) -> Vec<G1Affine> {
    println!("\n ***************** Start fk() ****************");
    assert_eq!(coeffs.len(), powers_of_x.len(), "length should be equal");
    let n = coeffs.len();
    assert!(n.is_power_of_two());

    // Get first column of circulant matrix in length of 2 * len(coeffs)
    // For example: coeffs is [1, 2, 3, 4]
    // The first column of circulant matrix should be: [4, 0, 0, 0, 0, 0, 2, 3]
    let mut first_col = coeffs.to_vec();
    // [1, 2, 3, 4] -> [0, 2, 3, 4]
    first_col[0] = Scalar::from(0);
    // println!("first_col: {:?}", first_col);

    // get first column of circulant matrix in 2n size
    // 1. padding 0
    // [0, 2, 3, 4] -> [0, 0, 0, 0, 0, 2, 3, 4]
    first_col.splice(0..0, iter::repeat(Scalar::from(0)).take(n));
    // 2. roll by 1 to right
    // [0, 0, 0, 0, 0, 2, 3, 4] -> [4, 0, 0, 0, 0, 0, 2, 3]
    first_col.rotate_right(1);
    // println!("first_col: {:?}", first_col);
    

    // inverse srs: delete last one then inverse
    let mut inv_powers_of_x = powers_of_x[..n-1].to_vec();
    inv_powers_of_x.reverse();
    let group1_zero = G1Affine { x: Fq::zero(), y: Fq::zero()};
    inv_powers_of_x.push(group1_zero); // 假设 b.Z1 是 Scalar(0.0)

    // padding n 0s to the end
    let ec_neutral_vals = vec![group1_zero; n];
    inv_powers_of_x.extend(ec_neutral_vals);
    // println!("inv_powers_of_x: {:?}", inv_powers_of_x);

    
    // We have circulant matrix C, C = F_inv * diag(F * first_col) * F
    // F: DFT matrix, F_inv: inverse DFT matrix
    // We want to get Q_T_comm_poly_coeffs = C * x = F_inv * diag(F * first_col) * F * x
    // 1. right hand side: F * x
    let rhs = ec_fft(&mut inv_powers_of_x);

    // 2. middle hand side: F * first_col
    let mhs = fft(&mut first_col);

    // middle * right (element wise) to get diagonal: diag(F * first_col) * F * x
    let m_r_hs: Vec<G1Affine> = rhs.iter().zip(mhs.iter()).map(|(&r, &m)|(r * m).into()).collect();

    // 3. ifft
    let result = ec_ifft(&mut m_r_hs.clone());

    // 4. return first n values
    let q_comm_poly_coeffs = result[..n].to_vec();
    println!("\n ***************** End fk() ****************");
    q_comm_poly_coeffs
}

pub fn precompute_with_fk(
    table: &Vec<Fr>,
    powers_of_x: &mut Vec<G1Affine>,
) -> Vec<G1Affine> {
    // Convert table values to Scalars
    let t_values: Vec<Scalar> = table.iter().map(|&val| Scalar::from(val)).collect();
    
    // Compute t_poly_coeffs using inverse FFT
    let mut t_poly_coeffs = t_values.clone();
    t_poly_coeffs = ifft(&mut t_poly_coeffs);

    // Compute h values with fk
    fk(&mut t_poly_coeffs, powers_of_x)
}

#[cfg(test)]
mod tests {
    use crate::backend::cq::preprocessor::preprocess;
    use super::*;

    #[test]
    fn test_preprocess() {
        let table = vec![Fr::from(1), Fr::from(2), Fr::from(3), Fr::from(4)];
        let (param, pp, vp, q_t_comm_poly_coeffs) = preprocess(4, 4, &table).unwrap();
        println!("param: {:?}", param);
        println!("pp: {:?}", pp);
        println!("vp: {:?}", vp);
        println!("q_t_comm_poly_coeffs: {:?}", q_t_comm_poly_coeffs);
    }
}
