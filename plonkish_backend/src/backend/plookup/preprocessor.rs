use crate::{
    pcs::PolynomialCommitmentScheme,
    util::arithmetic::PrimeField,
    poly::univariate::UnivariatePolynomial,
    Error,
};
use super::{
    PlookupProverParam,
    PlookupVerifierParam,
    PlookupInfo,
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
    let (pcs_pp, pcs_vp) = Pcs::trim(param, order*4, 1)?;
    let g = get_root_of_power_of_2_order(info.k)?;
    let pp: PlookupProverParam<F, Pcs> = PlookupProverParam {
        pcs: pcs_pp,
        g: g,
        table: info.table.clone(),
        lookup: info.lookup.clone(),
    };
    let vp: PlookupVerifierParam<F, Pcs> = PlookupVerifierParam {
        pcs: pcs_vp,
        g: g,
        table: info.table.clone(),
    };
    Ok((pp, vp))
}

/// get root of order 2^n of a primefield.
/// require that the order of the primefield is a multiplicative of 2^n
pub(super) fn get_root_of_power_of_2_order<F: PrimeField>(n: u32) -> Result<F, Error> {
    let s = F::S;
    if n > s {
        return Err(Error::InvalidPcsParam("invalid order".to_string()))
    }
    let mut u = F::ROOT_OF_UNITY;
    let mut i = n;
    while i < s {
        u = u.square();
        i += 1;
    }
    Ok(u)
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_curves::bn256::{Bn256, Fr};
    use crate::{
        pcs::univariate::UnivariateKzg,
        util::test::std_rng,
    };

    type Pcs = UnivariateKzg<Bn256>;

    #[test]
    fn test_preprocess() {
        let mut rng = std_rng();
        let k = 2;
        let n = 1 << k;
        let table = vec![Fr::one(), Fr::from(2), Fr::from(3), Fr::from(4)];
        assert_eq!(n, table.len());
        let lookup = vec![Fr::one(), Fr::one(), Fr::from(2)];
        let param = Pcs::setup(n, 1, &mut rng).unwrap();
        let info = PlookupInfo{k, table, lookup};
        let (_pp, _vp) = preprocess::<Fr, Pcs>(&param, &info).unwrap();
    }
}
