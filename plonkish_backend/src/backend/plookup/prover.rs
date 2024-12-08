use halo2_curves::ff::WithSmallOrderMulGroup;

use crate::{
    backend::plookup::{PlookupProverParam, PlookupVerifierParam, PlookupInfo},
    pcs::PolynomialCommitmentScheme,
    poly::Polynomial,
    util::{
        arithmetic::PrimeField,
        test::std_rng,
    },
    poly::univariate::{UnivariateBasis, UnivariatePolynomial},
    Error,
};

pub(super) fn sorted_by_table<F: PrimeField>(
    table: &Vec<F>,
    witness: &Vec<F>,
) -> Vec<F> {
    let n = table.len();
    let count = {
        let mut ret = vec![1; table.len()];
        for w in witness {
            let mut i = 0;
            while i < n {
                if *w == table[i] {
                    ret[i] += 1;
                    break;
                }
                i += 1;
            }
            assert!(i < n); // ensure w in table
        }
        ret
    };
    let sorted = {
        let mut ret: Vec<F> = Vec::with_capacity(n+witness.len());
        let mut i = 0;
        while i < n {
            let mut cnt = count[i];
            while cnt > 0 {
                ret.push(table[i]);
                cnt -= 1;
            }
            i += 1;
        }
        ret
    }; 
    sorted
}

pub(super) fn compute_inner_polynomial<F: PrimeField>(
    beta: &F,
    gamma: &F,
    f: &Vec<F>,
    t: &Vec<F>,
    s: &Vec<F>,
) -> UnivariatePolynomial<F> {
    let n = t.len();
    let mut numer = F::ONE;
    let mut denom = F::ONE;
    let values = {
        let mut ret: Vec<F> = Vec::with_capacity(n);
        ret.push(F::ONE);
        let mut i = 1;
        while i < n {
            numer = numer * (F::ONE+*beta) * (*gamma+f[i-1])
                * (*gamma*(F::ONE+*beta)+t[i-1]+*beta*t[i]);
            denom = denom * (*gamma*(F::ONE+*beta)+s[i-1]+*beta*s[i])
                * (*gamma*(F::ONE+*beta)+s[n+i-2]+*beta*s[n+i-1]);
            i += 1;
            ret.push(numer*F::invert(&denom).unwrap());
        }
        assert!(ret[n-1] == F::ONE);
        ret
    };
    UnivariatePolynomial::lagrange(values)
}

pub(super) fn compute_quotient_polynomial<F: PrimeField+WithSmallOrderMulGroup<3>>(
    beta: &F,
    gamma: &F,
    delta: &F,
    t: &UnivariatePolynomial<F>,
    f: &UnivariatePolynomial<F>,
    s: &UnivariatePolynomial<F>,
    h1: &UnivariatePolynomial<F>,
    h2: &UnivariatePolynomial<F>,
    z: &UnivariatePolynomial<F>,
) -> UnivariatePolynomial<F> {
    let n = t.coeffs().len();
    let l0_poly = {
        let mut values = vec![F::ZERO; n];
        values[0] = F::ONE;
        UnivariatePolynomial::lagrange(values).ifft()
    };
    let ln_poly = {
        let mut values = vec![F::ZERO; n];
        values[n-1] = F::ONE;
        UnivariatePolynomial::lagrange(values).ifft()
    };
    let z_minus_1 = z.ifft() + (-F::ONE);
    let poly_a = &l0_poly * &z_minus_1;
    let poly_b = {
        let front = UnivariatePolynomial::monomial(vec![-F::ONE, F::ONE]); // x-1
        let beta_plus_1 = F::ONE + beta;
        let lhs = z.ifft() * &beta_plus_1 * (f.ifft() + *gamma) *
            (t + t.shift(1) * beta + beta_plus_1 * gamma).ifft();
        let rhs = z.shift(1).ifft() * (h1 + h1.shift(1) * beta + beta_plus_1 * gamma).ifft()
            * (h2 + h2.shift(1) * beta + beta_plus_1 * gamma).ifft();
        front * (&lhs - &rhs)
    };
    let poly_c = &ln_poly * &(h1 - h2.shift(1).ifft());
    let poly_d = &ln_poly * &z_minus_1;
    aggregate(delta, vec![poly_a, poly_b, poly_c, poly_d])
}

fn aggregate<F: PrimeField>(
    scalar: &F,
    polys: Vec<UnivariatePolynomial<F>>,
) -> UnivariatePolynomial<F> {
    assert!(polys.len()>0);

    let mut result = polys[0].clone();
    let mut power = scalar.clone();
    for poly in polys[1..].iter() {
        result += poly * power;
        power *= scalar;
    }
    result
}

#[cfg(test)]
mod tests {
    use crate::{
        backend::plookup::prover::{sorted_by_table, PlookupVerifierParam},
        pcs::PolynomialCommitmentScheme,
        util::{
            arithmetic::PrimeField,
            test::std_rng,
        },
    };
    use crate::pcs::univariate::UnivariateKzg;
    use halo2_curves::{bn256::{Bn256, Fr}, ff::Field};

    use super::compute_inner_polynomial; // Use Fr for the field type

    type Pcs = UnivariateKzg<Bn256>;

    #[test]
    fn test_sorted_by_table() {
        let lookup = vec![Fr::one(), Fr::one(), Fr::from(2)];
        let table = vec![Fr::one(), Fr::from(2), Fr::from(3), Fr::from(4)];
        let sorted = sorted_by_table(&table, &lookup);
        // println!("{:?}", sorted);
        let expected = vec![Fr::one(), Fr::one(), Fr::one(), Fr::from(2), Fr::from(2), Fr::from(3), Fr::from(4)];
        let is_the_same = {
            (sorted.len() == expected.len()) &&
            sorted.iter().zip(expected).all(|(a,b)| (*a==b))
        };
        assert!(is_the_same);
    }

    #[test]
    fn test_compute_inner_polynomial() {
        let lookup = vec![Fr::one(), Fr::one(), Fr::from(2)];
        let table = vec![Fr::one(), Fr::from(2), Fr::from(3), Fr::from(4)];
        let sorted = sorted_by_table(&table, &lookup);
        let mut rng = std_rng();
        let beta = Fr::random(&mut rng);
        let gamma = Fr::random(&mut rng);
        let poly = compute_inner_polynomial(
            &beta,
            &gamma,
            &lookup,
            &table,
            &sorted,
        );
        println!("{:#?}", poly);
    }
}
