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

pub(super) fn preprocess<F: PrimeField, Pcs: PolynomialCommitmentScheme<F, Polynomial = UnivariatePolynomial<F>>>(
    param: &Pcs::Param,
    info: &PlookupInfo<F>,
) -> Result<
    (
        PlookupProverParam<F, Pcs>,
        PlookupVerifierParam<F, Pcs>,
    ),
    Error> {
    let order = 1 << info.k;
    // let mut rng = std_rng();
    let (pcs_pp, pcs_vp) = Pcs::trim(param, order, 1)?;
    
    let g = {
        let mut u = F::ROOT_OF_UNITY;
        let mut i = info.k;
        let s = F::S;
        assert!(i <= s);
        while i < s {
            u = u.square();
            i += 1;
        }
        u
    };
    let roots = { // [g, g^2, ..., 1]
        let mut ret: Vec<F> = Vec::with_capacity(order);
        let mut i = 1;
        let mut now = g;
        while i < order {
            ret.push(now);
            now = now*g;
            i += 1;
        }
        assert_eq!(now, F::ONE);
        ret.push(now);
        ret
    };
    let pp: PlookupProverParam<F, Pcs> = PlookupProverParam {
        pcs: pcs_pp,
        g: g,
    };
    let vp: PlookupVerifierParam<F, Pcs> = PlookupVerifierParam {
        pcs: pcs_vp,
        g: g,
    };
    Ok((pp, vp))
}

#[cfg(test)]
mod tests {
    use crate::{
        backend::plookup::{preprocessor::preprocess, PlookupVerifierParam},
        pcs::PolynomialCommitmentScheme,
        util::{
            arithmetic::PrimeField,
            test::std_rng,
        },
    };
    use crate::pcs::univariate::UnivariateKzg;
    use halo2_curves::{bn256::{Bn256, Fr}}; // Use Fr for the field type

    type Pcs = UnivariateKzg<Bn256>;

    #[test]
    fn test_preprocess() {
        let mut rng = std_rng();
        let k = 10;
        let n = 1 << k;
        let param = Pcs::setup(n, 1, &mut rng).unwrap();
        // let group = Fr::ZETA;
        // let (pp, vp) = preprocess::<Fr, Pcs>(&param, n).unwrap(); // Explicitly specify Fr for F

        assert!(true);
    }
}
