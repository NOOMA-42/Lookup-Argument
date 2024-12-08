use crate::{
    pcs::Additive,
    poly::{univariate::UnivariateBasis::*, Polynomial},
    util::{
        arithmetic::{div_ceil, horner, powers, radix2_fft, root_of_unity, root_of_unity_inv, Field, WithSmallOrderMulGroup},
        impl_index, izip_eq,
        parallel::{num_threads, parallelize, parallelize_iter},
        Deserialize, Itertools, Serialize,
    },
};
use halo2_curves::ff::PrimeField;
use std::ops::{Div, DivAssign};
use std::{
    borrow::Borrow,
    cmp::Ordering::{Equal, Greater, Less},
    fmt::Debug,
    iter::Sum,
    mem,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnivariateBasis {
    Monomial,
    Lagrange,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnivariatePolynomial<F> {
    basis: UnivariateBasis,
    coeffs: Vec<F>,
}

impl<F> Default for UnivariatePolynomial<F> {
    fn default() -> Self {
        UnivariatePolynomial::zero()
    }
}

impl<F: Field> Additive<F> for UnivariatePolynomial<F> {
    fn msm<'a, 'b>(
        scalars: impl IntoIterator<Item=&'a F>,
        bases: impl IntoIterator<Item=&'b Self>,
    ) -> Self
    where
        Self: 'b,
    {
        izip_eq!(scalars, bases).sum()
    }
}

impl<F> UnivariatePolynomial<F> {
    pub const fn zero() -> Self {
        Self {
            basis: Monomial,
            coeffs: Vec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.coeffs.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item=&F> {
        self.coeffs.iter()
    }

    pub fn coeffs(&self) -> &[F] {
        self.coeffs.as_slice()
    }

    pub fn coeffs_mut(&mut self) -> &mut [F] {
        self.coeffs.as_mut_slice()
    }

    pub fn into_coeffs(self) -> Vec<F> {
        self.coeffs
    }

    pub fn degree(&self) -> usize {
        assert_eq!(self.basis, Monomial);

        self.coeffs().len().checked_sub(1).unwrap_or_default()
    }
}

impl<F: Field> Polynomial<F> for UnivariatePolynomial<F> {
    type Point = F;

    fn coeffs(&self) -> &[F] {
        &self.coeffs
    }

    fn evaluate(&self, point: &Self::Point) -> F {
        UnivariatePolynomial::evaluate(self, point)
    }

    #[cfg(any(test, feature = "benchmark"))]
    fn rand(n: usize, rng: impl rand::RngCore) -> Self {
        Self::monomial(crate::util::test::rand_vec(n, rng))
    }

    #[cfg(any(test, feature = "benchmark"))]
    fn rand_point(_: usize, rng: impl rand::RngCore) -> F {
        F::random(rng)
    }

    #[cfg(any(test, feature = "benchmark"))]
    fn squeeze_point(
        _: usize,
        transcript: &mut impl crate::util::transcript::FieldTranscript<F>,
    ) -> Self::Point {
        transcript.squeeze_challenge()
    }
}

impl<F: Field> UnivariatePolynomial<F> {
    pub fn monomial(coeffs: Vec<F>) -> Self {
        let mut poly = Self {
            basis: Monomial,
            coeffs,
        };
        poly.truncate_leading_zeros();
        poly
    }

    pub fn lagrange(coeffs: Vec<F>) -> Self {
        assert!(coeffs.len().is_power_of_two());

        Self {
            basis: Lagrange,
            coeffs,
        }
    }

    pub fn vanishing<'a>(points: impl IntoIterator<Item=&'a F>, scalar: F) -> Self {
        let points = points.into_iter().collect_vec();
        assert!(!points.is_empty());

        let mut buf;
        let mut coeffs = vec![F::ZERO; points.len() + 1];
        *coeffs.last_mut().unwrap() = scalar;
        for (point, len) in points.into_iter().zip(2..) {
            buf = scalar;
            for idx in (0..coeffs.len() - 1).rev().take(len) {
                buf = coeffs[idx] - buf * point;
                mem::swap(&mut buf, &mut coeffs[idx]);
            }
        }
        Self::monomial(coeffs)
    }

    pub fn basis(&self) -> UnivariateBasis {
        self.basis
    }

    pub fn evaluate(&self, x: &F) -> F {
        assert_eq!(self.basis, Monomial);

        let num_threads = num_threads();
        if self.coeffs().len() < num_threads {
            return horner(&self.coeffs, x);
        }

        let chunk_size = div_ceil(self.coeffs().len(), num_threads);
        let mut results = vec![F::ZERO; num_threads];
        parallelize_iter(
            results
                .iter_mut()
                .zip(self.coeffs.chunks(chunk_size))
                .zip(powers(x.pow_vartime([chunk_size as u64]))),
            |((result, coeffs), scalar)| *result = horner(coeffs, x) * scalar,
        );
        results.iter().fold(F::ZERO, |acc, result| acc + result)
    }

    pub fn div_rem(&self, divisor: &Self) -> (Self, Self) {
        assert_eq!(self.basis, Monomial);

        match (self.is_empty(), divisor.is_empty()) {
            (_, true) => unreachable!(),
            (true, _) => (Self::zero(), Self::zero()),
            (_, _) => {
                if self.degree() < divisor.degree() {
                    return (Self::zero(), self.clone());
                }

                let mut quotient = vec![F::ZERO; self.degree() - divisor.degree() + 1];
                let mut remainder = self.clone();
                let divisor_leading_inv = divisor.coeffs().last().unwrap().invert().unwrap();
                while remainder.degree() >= divisor.degree() {
                    let quotient_coeff = divisor_leading_inv * remainder.coeffs().last().unwrap();
                    let degree = remainder.degree() - divisor.degree();
                    quotient[degree] = quotient_coeff;
                    for (idx, coeff) in divisor.coeffs.iter().enumerate() {
                        remainder[degree + idx] -= &(quotient_coeff * coeff);
                    }
                    remainder.truncate_leading_zeros();
                }
                (Self::monomial(quotient), remainder)
            }
        }
    }

    fn truncate_leading_zeros(&mut self) {
        assert_eq!(self.basis, Monomial);

        self.coeffs.truncate(
            self.coeffs
                .iter()
                .rev()
                .position(|coeff| !coeff.is_zero_vartime())
                .map(|num_zeros| self.coeffs.len() - num_zeros)
                .unwrap_or_default(),
        );
    }

    pub fn poly_mul(&self, rhs: UnivariatePolynomial<F>) -> UnivariatePolynomial<F>
    where
        F: Field + WithSmallOrderMulGroup<3>
    {
        assert_eq!(self.basis, Monomial);
        assert_eq!(rhs.basis, Monomial);

        let n = self.coeffs.len() + rhs.coeffs.len() - 1;
        let size = n.next_power_of_two();
        let log_size = size.trailing_zeros() as usize;

        let mut self_padded = self.coeffs.to_vec();
        let mut rhs_padded = rhs.coeffs.to_vec();
        self_padded.resize(size, F::ZERO);
        rhs_padded.resize(size, F::ZERO);

        let omega = root_of_unity(log_size);
        let omega_inv = root_of_unity_inv(log_size);

        radix2_fft(&mut self_padded, omega, log_size);
        radix2_fft(&mut rhs_padded, omega, log_size);

        let mut result = self_padded.iter().zip(rhs_padded.iter()).map(|(&x, &y)| x * y).collect::<Vec<_>>();

        radix2_fft(&mut result, omega_inv, log_size);

        let size_inv = F::from(size as u64).invert().unwrap();
        result.iter_mut().for_each(|x| *x *= size_inv);
        result.truncate(n);
        UnivariatePolynomial::monomial(result)
    }

    pub fn fft(&self) -> UnivariatePolynomial<F>
    where
        F: Field + WithSmallOrderMulGroup<3>
    {
        assert_eq!(self.basis, Monomial);

        let mut result = self.coeffs.clone();
        let n = result.len();
        let size = n.next_power_of_two();
        result.resize(size, F::ZERO);

        let log_size = size.trailing_zeros() as usize;
        let omega = root_of_unity(log_size);

        radix2_fft(&mut result, omega, log_size);

        UnivariatePolynomial::lagrange(result)
    }

    pub fn ifft(&self) -> UnivariatePolynomial<F>
    where
        F: Field + WithSmallOrderMulGroup<3>
    {
        assert_eq!(self.basis, Lagrange);
        assert!(self.coeffs.len().is_power_of_two());

        let mut result = self.coeffs.clone();
        let size = result.len();
        let log_size = size.trailing_zeros() as usize;
        let size_inv = F::from(size as u64).invert().unwrap();
        let omega_inv = root_of_unity_inv(log_size);

        radix2_fft(&mut result, omega_inv, log_size);
        result.iter_mut().for_each(|x| *x *= size_inv);
        result.truncate(size);

        UnivariatePolynomial::monomial(result)
    }

    pub fn shift(&self, n: i32) -> UnivariatePolynomial<F>
    where
        F: Field
    {
        assert_eq!(self.basis, Lagrange);

        let size = self.coeffs.len();
        let now = {
            let remain = n%(size as i32);
            if remain < 0 {
                (remain+size as i32) as usize
            } else {
                remain as usize
            }
        };
        let result = self.coeffs[now..]
            .iter()
            .chain(self.coeffs[..now].iter())
            .cloned()
            .collect();
        UnivariatePolynomial::lagrange(result)
    }
}

impl<F: Field> Neg for UnivariatePolynomial<F> {
    type Output = UnivariatePolynomial<F>;

    fn neg(mut self) -> Self::Output {
        self.coeffs.iter_mut().for_each(|coeff| *coeff = -*coeff);
        self
    }
}

impl<F: Field> Add<F> for UnivariatePolynomial<F> {
    type Output = UnivariatePolynomial<F>;

    fn add(self, rhs: F) -> UnivariatePolynomial<F> {
        let mut coeffs = self.coeffs;
        match self.basis {
            Monomial => {
                coeffs[0] += rhs;
                UnivariatePolynomial::monomial(coeffs)
            },
            Lagrange => {
                coeffs.iter_mut().for_each(|coeff| *coeff += rhs);
                UnivariatePolynomial::lagrange(coeffs)
            },
        }
    }
}

impl<F: Field, P: Borrow<UnivariatePolynomial<F>>> Add<P> for &UnivariatePolynomial<F> {
    type Output = UnivariatePolynomial<F>;

    fn add(self, rhs: P) -> UnivariatePolynomial<F> {
        let mut output = self.clone();
        output += rhs;
        output
    }
}

impl<F: Field, P: Borrow<UnivariatePolynomial<F>>> AddAssign<P> for UnivariatePolynomial<F> {
    fn add_assign(&mut self, rhs: P) {
        let rhs = rhs.borrow();
        assert_eq!(self.basis, rhs.basis);

        match self.basis {
            Monomial => match self.degree().cmp(&rhs.degree()) {
                Less => {
                    parallelize(&mut self.coeffs, |(lhs, start)| {
                        for (lhs, rhs) in lhs.iter_mut().zip(rhs[start..].iter()) {
                            *lhs += rhs;
                        }
                    });
                    self.coeffs
                        .extend(rhs[self.coeffs().len()..].iter().cloned());
                }
                ord @ (Greater | Equal) => {
                    parallelize(&mut self[..rhs.coeffs().len()], |(lhs, start)| {
                        for (lhs, rhs) in lhs.iter_mut().zip(rhs[start..].iter()) {
                            *lhs += rhs;
                        }
                    });
                    if matches!(ord, Equal) {
                        self.truncate_leading_zeros();
                    }
                }
            },
            Lagrange => {
                assert_eq!(self.coeffs.len(), rhs.coeffs.len());

                parallelize(&mut self.coeffs, |(lhs, start)| {
                    for (lhs, rhs) in lhs.iter_mut().zip(rhs[start..].iter()) {
                        *lhs += rhs;
                    }
                });
            }
        }
    }
}

impl<F: Field, BF: Borrow<F>, P: Borrow<UnivariatePolynomial<F>>> AddAssign<(BF, P)>
for UnivariatePolynomial<F>
{
    fn add_assign(&mut self, (scalar, rhs): (BF, P)) {
        let (scalar, rhs) = (scalar.borrow(), rhs.borrow());
        assert_eq!(self.basis, rhs.basis);

        if scalar == &F::ONE {
            *self += rhs;
        } else if scalar == &-F::ONE {
            *self -= rhs;
        } else if scalar != &F::ZERO {
            match self.basis {
                Monomial => match self.degree().cmp(&rhs.degree()) {
                    Less => {
                        parallelize(&mut self.coeffs, |(lhs, start)| {
                            let scalar = *scalar;
                            for (lhs, rhs) in lhs.iter_mut().zip(rhs[start..].iter()) {
                                *lhs += scalar * rhs;
                            }
                        });
                        self.coeffs
                            .extend(rhs[self.coeffs().len()..].iter().map(|rhs| *rhs * scalar));
                    }
                    ord @ (Greater | Equal) => {
                        parallelize(&mut self[..rhs.coeffs().len()], |(lhs, start)| {
                            let scalar = *scalar;
                            for (lhs, rhs) in lhs.iter_mut().zip(rhs[start..].iter()) {
                                *lhs += scalar * rhs;
                            }
                        });
                        if matches!(ord, Equal) {
                            self.truncate_leading_zeros();
                        }
                    }
                },
                Lagrange => {
                    assert_eq!(self.coeffs.len(), rhs.coeffs.len());

                    parallelize(&mut self.coeffs, |(lhs, start)| {
                        let scalar = *scalar;
                        for (lhs, rhs) in lhs.iter_mut().zip(rhs[start..].iter()) {
                            *lhs += scalar * rhs;
                        }
                    });
                }
            }
        }
    }
}

impl<F: Field, P: Borrow<UnivariatePolynomial<F>>> Sub<P> for &UnivariatePolynomial<F> {
    type Output = UnivariatePolynomial<F>;

    fn sub(self, rhs: P) -> UnivariatePolynomial<F> {
        let mut output = self.clone();
        output -= rhs;
        output
    }
}

impl<F: Field, P: Borrow<UnivariatePolynomial<F>>> SubAssign<P> for UnivariatePolynomial<F> {
    fn sub_assign(&mut self, rhs: P) {
        let rhs = rhs.borrow();
        assert_eq!(self.basis, rhs.basis);

        match self.basis {
            Monomial => match self.degree().cmp(&rhs.degree()) {
                Less => {
                    parallelize(&mut self.coeffs, |(lhs, start)| {
                        for (lhs, rhs) in lhs.iter_mut().zip(rhs[start..].iter()) {
                            *lhs -= rhs;
                        }
                    });
                    self.coeffs
                        .extend(rhs[self.coeffs().len()..].iter().cloned().map(Neg::neg));
                }
                ord @ (Greater | Equal) => {
                    parallelize(&mut self[..rhs.coeffs().len()], |(lhs, start)| {
                        for (lhs, rhs) in lhs.iter_mut().zip(rhs[start..].iter()) {
                            *lhs -= rhs;
                        }
                    });
                    if matches!(ord, Equal) {
                        self.truncate_leading_zeros();
                    }
                }
            },
            Lagrange => {
                assert_eq!(self.coeffs.len(), rhs.coeffs.len());

                parallelize(&mut self.coeffs, |(lhs, start)| {
                    for (lhs, rhs) in lhs.iter_mut().zip(rhs[start..].iter()) {
                        *lhs -= rhs;
                    }
                });
            }
        }
    }
}

impl<F: Field, BF: Borrow<F>, P: Borrow<UnivariatePolynomial<F>>> SubAssign<(BF, P)>
for UnivariatePolynomial<F>
{
    fn sub_assign(&mut self, (scalar, rhs): (BF, P)) {
        *self += (-*scalar.borrow(), rhs);
    }
}

impl<F: Field> Mul<F> for &UnivariatePolynomial<F> {
    type Output = UnivariatePolynomial<F>;

    fn mul(self, rhs: F) -> UnivariatePolynomial<F> {
        self * &rhs
    }
}

// using &F instead of Borrow<F> to avoid conflicts with Mul<Self>
impl<F: Field> Mul<&F> for &UnivariatePolynomial<F> {
    type Output = UnivariatePolynomial<F>;

    fn mul(self, rhs: &F) -> UnivariatePolynomial<F> {
        let mut output = self.clone();
        output *= rhs;
        output
    }
}

impl<F: Field> Mul<&F> for UnivariatePolynomial<F> {
    type Output = UnivariatePolynomial<F>;

    fn mul(self, rhs: &F) -> UnivariatePolynomial<F> {
        &self * rhs
    }
}

impl<F: Field> MulAssign<&F> for UnivariatePolynomial<F> {
    fn mul_assign(&mut self, rhs: &F) {
        if rhs == &F::ZERO {
            match self.basis {
                Monomial => self.coeffs.clear(),
                Lagrange => self.coeffs.fill(F::ZERO),
            }
        } else if rhs != &F::ONE {
            parallelize(&mut self.coeffs, |(lhs, _)| {
                for lhs in lhs.iter_mut() {
                    *lhs *= rhs;
                }
            });
        }
    }
}

impl<F: Field> Mul for UnivariatePolynomial<F> {
    type Output = UnivariatePolynomial<F>;

    fn mul(mut self, rhs: UnivariatePolynomial<F>) -> UnivariatePolynomial<F> {
        self *= &rhs;
        self
    }
}

impl<F: Field> MulAssign for UnivariatePolynomial<F> {
    fn mul_assign(&mut self, rhs: Self) {
        *self *= &rhs;
    }
}

impl<F: Field> Mul for &UnivariatePolynomial<F> {
    type Output = UnivariatePolynomial<F>;

    fn mul(self, rhs: &UnivariatePolynomial<F>) -> UnivariatePolynomial<F> {
        let mut output = self.clone();
        output *= rhs;
        output
    }
}

impl<F: Field> MulAssign<&Self> for UnivariatePolynomial<F> {
    fn mul_assign(&mut self, rhs: &Self) {
        if self.is_empty() || rhs.is_empty() {
            *self = UnivariatePolynomial::zero();
            return;
        }

        assert_eq!(self.basis, Monomial);
        assert_eq!(rhs.basis, Monomial);

        let mut result_coeffs = vec![F::ZERO; self.coeffs().len() + rhs.coeffs().len() - 1];

        for (i, &self_coeff) in self.coeffs().iter().enumerate() {
            for (j, &rhs_coeff) in rhs.coeffs().iter().enumerate() {
                result_coeffs[i + j] += self_coeff * rhs_coeff;
            }
        }

        self.coeffs = result_coeffs;
    }
}

impl<F: Field> Div for &UnivariatePolynomial<F> {
    type Output = UnivariatePolynomial<F>;

    fn div(self, rhs: &UnivariatePolynomial<F>) -> Self::Output {
        let mut output = self.clone();
        output /= rhs;
        output
    }
}

impl<F: Field> DivAssign<&UnivariatePolynomial<F>> for UnivariatePolynomial<F> {
    fn div_assign(&mut self, rhs: &UnivariatePolynomial<F>) {
        let (quotient, remainder) = self.clone().div_rem(&rhs);
        assert_eq!(remainder, UnivariatePolynomial::zero());
        *self = quotient;
    }
}

impl<F: Field, P: Borrow<UnivariatePolynomial<F>>> Sum<P> for UnivariatePolynomial<F> {
    fn sum<I: Iterator<Item=P>>(mut iter: I) -> UnivariatePolynomial<F> {
        let init = match (iter.next(), iter.next()) {
            (Some(lhs), Some(rhs)) => lhs.borrow() + rhs.borrow(),
            (Some(lhs), None) => return lhs.borrow().clone(),
            _ => return Self::zero(),
        };
        iter.fold(init, |mut acc, poly| {
            acc += poly.borrow();
            acc
        })
    }
}

impl<F: Field, BF: Borrow<F>, P: Borrow<UnivariatePolynomial<F>>> Sum<(BF, P)>
for UnivariatePolynomial<F>
{
    fn sum<I: Iterator<Item=(BF, P)>>(mut iter: I) -> UnivariatePolynomial<F> {
        let init = match iter.next() {
            Some((scalar, poly)) => {
                let mut poly = poly.borrow().clone();
                poly *= scalar.borrow();
                poly
            }
            _ => return Self::zero(),
        };
        iter.fold(init, |mut acc, (scalar, poly)| {
            acc += (scalar.borrow(), poly.borrow());
            acc
        })
    }
}

impl_index!(UnivariatePolynomial, coeffs);

impl<F: PrimeField> From<Vec<u64>> for UnivariatePolynomial<F> {
    fn from(nums: Vec<u64>) -> Self {
        let coeffs = nums.iter().map(|&x| F::from(x)).collect();
        UnivariatePolynomial::monomial(coeffs)
    }
}

fn div<F: Field>(a: F, b: F) -> F {
    a * b.invert().expect("Division by zero")
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_curves::bn256::{Bn256, Fr};
    use halo2_curves::pairing::Engine;
    type Scalar = <Bn256 as Engine>::Scalar;

    #[test]
    fn test_scalar_add() {
        // monomial addition
        let p1 = UnivariatePolynomial::monomial(vec![Fr::from(1), Fr::from(2), Fr::from(3)]);
        let s = Fr::from(3);
        let p2 = p1.clone() + s;
        assert_eq!(p2.coeffs(), &[Fr::from(4), Fr::from(2), Fr::from(3)]);
        assert_eq!(p1.evaluate(&Fr::from(1)) + s, p2.evaluate(&Fr::from(1)));
        assert_eq!(p1.evaluate(&Fr::from(2)) + s, p2.evaluate(&Fr::from(2)));
        assert_eq!(p1.evaluate(&Fr::from(3)) + s, p2.evaluate(&Fr::from(3)));
        // lagrange addition
        let p3 = UnivariatePolynomial::lagrange(vec![Fr::from(1), Fr::from(2), Fr::from(3), Fr::from(4)]);
        let p4 = p3.clone() + s;
        assert_eq!(p4.coeffs(), &[Fr::from(4), Fr::from(5), Fr::from(6), Fr::from(7)]);
    }

    #[test]
    fn test_scalar_mul() {
        let p1 = UnivariatePolynomial::from(vec![1, 2, 3]);
        let s = Scalar::random(&mut rand::thread_rng());
        let p2 = &p1 * &s;
        let p3 = &p1 * s;

        let test_point = Scalar::random(&mut rand::thread_rng());
        assert_eq!(p1.evaluate(&test_point) * s, p2.evaluate(&test_point));
        assert_eq!(p1.evaluate(&test_point) * s, p3.evaluate(&test_point));
    }

    #[test]
    fn test_mul_div() {
        let p1 = UnivariatePolynomial::from(vec![1, 2, 3]);
        let p2 = UnivariatePolynomial::from(vec![0, 0, 1, 2, 3]);
        let p3 = &p1 * &p2;
        let p4 = &p2 / &p1;

        let test_point = Scalar::random(&mut rand::thread_rng());
        assert_eq!(p1.evaluate(&test_point) * p2.evaluate(&test_point), p3.evaluate(&test_point));
        assert_eq!(div(p2.evaluate(&test_point), p1.evaluate(&test_point)), p4.evaluate(&test_point));
    }

    #[test]
    fn test_mul_fft() {
        let p1: UnivariatePolynomial<Fr> = UnivariatePolynomial::from(vec![1, 2, 3]);
        let p2: UnivariatePolynomial<Fr> = UnivariatePolynomial::from(vec![0, 0, 1, 2, 3]);
        assert_eq!(p1.evaluate(&Fr::from(1)), Fr::from(6));
        assert_eq!(p1.evaluate(&Fr::from(2)), Fr::from(17));
        assert_eq!(p2.evaluate(&Fr::from(1)), Fr::from(6));
        assert_eq!(p2.evaluate(&Fr::from(2)), Fr::from(68));

        let p3: UnivariatePolynomial<Fr> = &p1 * &p2;
        let p4_fft: UnivariatePolynomial<Fr> = p1.poly_mul(p2);
        assert_eq!(p3, p4_fft);
    }

    #[test]
    fn test_fft_ifft() {
        let p1: UnivariatePolynomial<Fr> = UnivariatePolynomial::from(vec![1, 2, 3]);
        let p2 = p1.fft();
        let p3 = p2.ifft();
        assert_eq!(p1, p3);
        assert_eq!(p1.coeffs().len(), 3);
        // next power of 2
        assert_eq!(p2.coeffs().len(), 4);
        assert_eq!(p3.coeffs().len(), 3);

        let p4: UnivariatePolynomial<Fr> = UnivariatePolynomial::from(vec![1, 2, 3, 4, 5]);
        let p5 = p4.fft();
        let p6 = p5.ifft();
        assert_eq!(p4, p6);
        assert_eq!(p4.coeffs().len(), 5);
        // next power of 2
        assert_eq!(p5.coeffs().len(), 8);
        assert_eq!(p6.coeffs().len(), 5);
    }
}
