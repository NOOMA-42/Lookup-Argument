use std::ops::{Add};
use std::fmt;
use generic_array::typenum::False;
use rand::rngs::OsRng;
use num_integer::Roots;
use std::{fmt::Debug, collections::HashSet, ops::Mul};
use halo2_curves::bn256::{pairing, Bn256, Fr, G1Affine, G2Affine, G1, G2, Fq};
use crate::{
    poly::{Polynomial, univariate::UnivariatePolynomial},
    backend::baloo::{
      util::{lagrange_interp, multi_pairing},
    },
    backend::cq::{
        preprocessor::preprocess,
    },
    pcs::{
        PolynomialCommitmentScheme,
        Additive,
        univariate::{UnivariateKzg, UnivariateKzgParam, UnivariateKzgProverParam, UnivariateKzgVerifierParam, UnivariateKzgCommitment},
    },
    util::{
        arithmetic::{Field, PrimeField, root_of_unity, barycentric_weights},
        transcript::{InMemoryTranscript, TranscriptWrite, Keccak256Transcript, FieldTranscript, FieldTranscriptRead, FieldTranscriptWrite, G2TranscriptRead, G2TranscriptWrite},
    }
};

type Pcs = UnivariateKzg<Bn256>;
type Scalar = Fr;


fn is_power_of_two(n: usize) -> bool {
    (n & (n - 1)) == 0 && n != 0
}

pub fn log_2(n: usize) -> usize {
    assert_ne!(n, 0);

    if n.is_power_of_two() {
      (1usize.leading_zeros() - n.leading_zeros()) as usize
    } else {
      (0usize.leading_zeros() - n.leading_zeros()) as usize
    }
}

fn fft_general(values: &mut Vec<Scalar>, inv: bool) -> Vec<Scalar> {
    fn _fft(vals: &Vec<Scalar>, roots_of_unity: &Vec<Scalar>) -> Vec<Scalar> {
        if vals.len() == 1 {
            return vals.to_vec();
        }
        let L = _fft(&vals.iter().step_by(2).cloned().collect::<Vec<_>>(), &roots_of_unity.iter().step_by(2).cloned().collect::<Vec<_>>());
        let R = _fft(&vals.iter().skip(1).step_by(2).cloned().collect::<Vec<_>>(),  &roots_of_unity.iter().step_by(2).cloned().collect::<Vec<_>>());
        let mut o = vec![Fr::from(0); vals.len()];
        for (i, (x, y)) in L.iter().zip(R.iter()).enumerate() {
            let y_times_root = *y * roots_of_unity[i];
            o[i] = *x + y_times_root;
            o[i + L.len()] = *x - y_times_root;
        }
        o
    }

    assert!(values.len().is_power_of_two(), "fft: values length should be powers of 2");
    
    // let roots = Scalar::roots_of_unity(values.len());
    let log_values = log_2(values.len());
    let value_root_of_unity = root_of_unity::<Fr>(log_values);
    let roots = (0..values.len()).map(|i| value_root_of_unity.pow([i as u64])).collect::<Vec<Fr>>();

    // let o = Scalar::FIELD_MODULUS;
    let nvals: Vec<Fr> = values.clone();
    if inv {
        // Inverse FFT
        let invlen = Fr::from(values.len() as u64).invert().unwrap();
        let reversed_roots = [roots[0]].iter().cloned().chain(roots.iter().skip(1).rev().cloned()).collect::<Vec<_>>();
        _fft(&nvals, &reversed_roots).iter().map(|x| *x * invlen).collect()
    } else {
        // Regular FFT
        _fft(&nvals, &roots)
    }
}

pub fn ifft(values: &mut Vec<Scalar>) -> Vec<Scalar> {
    fft_general(values, true)
}

pub fn fft(values: &mut Vec<Scalar>) -> Vec<Scalar> {
    fft_general(values, false)
}

fn ec_fft_general(values: &mut Vec<G1Affine>, inv: bool) -> Vec<G1Affine> {
    fn _fft(vals: &Vec<G1Affine>, roots_of_unity: &Vec<Scalar>) -> Vec<G1Affine> {
        if vals.len() == 1 {
            return vals.to_vec();
        }
        let L = _fft(&vals.iter().step_by(2).cloned().collect::<Vec<_>>(), &roots_of_unity.iter().step_by(2).cloned().collect::<Vec<_>>());
        let R = _fft(&vals.iter().skip(1).step_by(2).cloned().collect::<Vec<_>>(), &roots_of_unity.iter().step_by(2).cloned().collect::<Vec<_>>());
        let mut o = vec![G1Affine { x: Fq::zero(), y: Fq::zero()}; vals.len()];

        for (i, (x, y)) in L.iter().zip(R.iter()).enumerate() {
            let y_times_root = y * roots_of_unity[i];
            o[i] = (x + y_times_root).into();
            o[i + L.len()] = (x - y_times_root).into();
        }
        o
    }

    assert!(is_power_of_two(values.len()), "ec_fft: values length should be powers of 2");
    
    let log_values: usize = log_2(values.len());
    let value_root_of_unity = root_of_unity::<Fr>(log_values);
    let roots = (0..values.len()).map(|i| value_root_of_unity.pow([i as u64])).collect::<Vec<Fr>>();

    let nvals: Vec<G1Affine> = values.iter().cloned().collect();
    if inv {
        // Inverse FFT
        let invlen = Fr::from(values.len() as u64).invert().unwrap();
        let reversed_roots = [roots[0]].iter().cloned().chain(roots.iter().skip(1).rev().cloned()).collect::<Vec<_>>();
        _fft(&nvals, &reversed_roots).iter().map(|x| (x * invlen).into()).collect()
    } else {
        // Regular FFT
        _fft(&nvals, &roots)
    }
}

pub fn ec_fft(values: &mut Vec<G1Affine>) -> Vec<G1Affine> {
    ec_fft_general(values, false)
}

pub fn ec_ifft(values: &mut Vec<G1Affine>) -> Vec<G1Affine> {
    ec_fft_general(values, true)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fft() {
        let mut values = vec![Fr::from(1), Fr::from(2), Fr::from(3), Fr::from(4)];
        let mut orig_fft = fft(&mut values);
        println!("FFT result: {:?}", orig_fft);

        let orig_from_ifft = ifft(&mut orig_fft);
        println!("IFFT result: {:?}", orig_from_ifft);
    }

    #[test]
    fn test_ec_fft() {
        let lookup = vec![Fr::from(1), Fr::from(2), Fr::from(2), Fr::from(3)];
        let table = vec![Fr::from(1), Fr::from(2), Fr::from(3), Fr::from(4)];
    
        let m = lookup.len();
        let t = table.len();

        let (param, pp, vp, q_t_comm_poly_coeffs) = preprocess(t, m, &table).unwrap();
        let mut powers_of_x = pp.monomial_g1()[..t].to_vec();
        let mut orig_ec_fft = ec_fft(&mut powers_of_x);
        println!("EC FFT result: {:?}", orig_ec_fft);

        let orig_from_ec_ifft = ec_ifft(&mut orig_ec_fft);
        println!("EC IFFT result: {:?}", orig_from_ec_ifft);
    }
}


