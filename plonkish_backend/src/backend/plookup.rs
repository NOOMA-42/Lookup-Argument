use halo2_proofs::transcript;
use rand::{rngs::OsRng, RngCore};
use std::{fmt::Debug, hash::Hash, marker::PhantomData};

use halo2_curves::{bn256::Bn256, ff::WithSmallOrderMulGroup};

use crate::{
    backend::{
        plookup::{
            preprocessor::preprocess,
            prover::{sorted_by_table, compute_inner_polynomial, compute_quotient_polynomial},
        },
        PlonkishBackend, PlonkishCircuit, PlonkishCircuitInfo,
    },
    poly::Polynomial,
    poly::univariate::UnivariatePolynomial,
    pcs::{
        PolynomialCommitmentScheme,
        univariate::{UnivariateKzg, UnivariateKzgParam, UnivariateKzgProverParam, UnivariateKzgVerifierParam},
    },
    util::{
        arithmetic::{Field, PrimeField, MultiMillerLoop, root_of_unity},
        expression::Expression,
        test::std_rng,
        Deserialize, DeserializeOwned, Itertools, Serialize,
        transcript::{InMemoryTranscript, TranscriptRead, TranscriptWrite, Keccak256Transcript},
    },
    Error,
};


pub mod preprocessor;
pub mod prover;
pub mod verifier;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PlookupProverParam <F, Pcs>
where
    F: PrimeField,
    Pcs: PolynomialCommitmentScheme<F>,
{
    pub(crate) pcs: Pcs::ProverParam,
    pub(crate) g: F,
    // pub(crate) lookup: Vec<(Expression<F>, Expression<F>)>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PlookupVerifierParam<F, Pcs>
where
    F: PrimeField,
    Pcs: PolynomialCommitmentScheme<F>,
{
    pub(crate) pcs: Pcs::VerifierParam,
    pub(crate) g: F,
    // pub(crate) preprocess_comms: Vec<Pcs::Commitment>,
}

// Todo: use PlonkishCircuitInfo instead
#[derive(Clone, Debug)]
pub struct PlookupInfo<F> {
    k: u32,
    table: Vec<F>,
    witness: Vec<F>,
}

#[derive(Clone, Debug)]
pub struct Plookup<F, Pcs>(PhantomData<F>, PhantomData<Pcs>);

impl<F, Pcs> Plookup<F, Pcs>
where
    F: PrimeField + WithSmallOrderMulGroup<3> + Hash + Serialize + DeserializeOwned,
    Pcs: PolynomialCommitmentScheme<F, Polynomial = UnivariatePolynomial<F>>,
{
    fn preprocess(
        param: &Pcs::Param,
        info: &PlookupInfo<F>,
    ) -> Result<
        (
            PlookupProverParam<F, Pcs>,
            PlookupVerifierParam<F, Pcs>,
        ), 
        Error> {
        preprocess(param, info)
    }

    fn prove(
        pp: PlookupProverParam<F, Pcs>,
        info: &PlookupInfo<F>,
        transcript: &mut impl TranscriptWrite<Pcs::CommitmentChunk, F>,
    ) -> Result<(), Error> {
        let order = 1 << info.k;
        let table = info.table.clone();
        let table_len = table.len();
        assert_eq!(order, table_len);
        let mut witness = info.witness.clone();
        let witness_len = witness.len();
        assert!(witness_len < table_len);
        // pad witness to length table_len-1
        let last = witness[witness_len-1];
        while witness.len() < table_len-1 {
            witness.push(last);
        }
        let s = sorted_by_table(&table, &witness);
        let h1 = {
            let mut ret: Vec<F> = Vec::new();
            let mut i = 0;
            while i < table_len {
                ret.push(s[i]);
                i += 1;
            }
            ret
        };
        let h2 = {
            let mut ret: Vec<F> = Vec::new();
            let mut i = table_len-1;
            while i < table_len*2-1 {
                ret.push(s[i]);
                i += 1;
            }
            ret
        };
        let t_poly = UnivariatePolynomial::lagrange(table.clone());
        witness.push(last); // pad witness to length order
        // todo: clone it before push
        let f_poly = UnivariatePolynomial::lagrange(witness.clone());
        let s_poly = UnivariatePolynomial::lagrange(s.clone());
        let h1_poly = UnivariatePolynomial::lagrange(h1);
        let h2_poly = UnivariatePolynomial::lagrange(h2);
        // let f_comm = Pcs::commit(&pp.pcs, &f_poly);
        // let h1_comm = Pcs::commit(&pp.pcs, &h1_poly);
        // let h2_comm = Pcs::commit(&pp.pcs, &h2_poly);
        let f_comm = Pcs::commit_and_write(&pp.pcs, &f_poly, transcript);
        let h1_comm = Pcs::commit_and_write(&pp.pcs, &h1_poly, transcript);
        let h2_comm = Pcs::commit_and_write(&pp.pcs, &h2_poly, transcript);
        let mut challenges: Vec<F> = Vec::with_capacity(2);
        challenges.extend(transcript.squeeze_challenges(2));
        let beta = &challenges[0];
        let gamma = &challenges[1];
        let z_poly = compute_inner_polynomial(beta, gamma, &witness, &table, &s);
        let z_comm = Pcs::commit_and_write(&pp.pcs, &z_poly, transcript);
        let delta = &transcript.squeeze_challenge();
        let q_poly = compute_quotient_polynomial(
            beta,
            gamma,
            delta,
            &t_poly,
            &f_poly,
            &s_poly,
            &h1_poly,
            &h2_poly,
            &z_poly,
        );
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashSet;
    use halo2_curves::bn256::Fr;
    use crate::util::transcript::{FieldTranscriptRead, FieldTranscriptWrite};
    use num_bigint::BigUint;

    type Pcs = UnivariateKzg<Bn256>;

    #[test]
    fn test_e2e() {
        let lookup = vec![Fr::one(), Fr::one(), Fr::from(2)];
        let table = vec![Fr::one(), Fr::from(2), Fr::from(3), Fr::from(4)];
        let m = lookup.len();
        let mut rng = std_rng();

        // Setup
        let (pp, vp) = {
            let mut rng = OsRng;
            let poly_size = m;
            print!("poly_size: {:?}\n", poly_size);
            let param = Pcs::setup(poly_size, 1, &mut rng).unwrap();
            Pcs::trim(&param, poly_size, 1).unwrap()
        };
        print!("lookup: {:?}\n", lookup);

        // Commit and open
        // let proof = {
        //     let mut transcript = Keccak256Transcript::new(());
        //     let poly = <Pcs as PolynomialCommitmentScheme<Fr>>::Polynomial::monomial(lookup.clone());
        //     print!("coeffs: {:?}\n", poly.coeffs());
        //     let comm = Pcs::commit_and_write(&pp, &poly, &mut transcript).unwrap();
        //     let point = <Pcs as PolynomialCommitmentScheme<Fr>>::Polynomial::squeeze_point(m, &mut transcript);
        //     let eval = poly.evaluate(&point);

        //     // Use the correct method to write the field element
        //     transcript.write_field_element(&eval).unwrap();

        //     Pcs::open(&pp, &poly, &comm, &point, &eval, &mut transcript).unwrap();
        //     transcript.into_proof()
        // };

        // Verify
        // let result = {
        //     let mut transcript = Keccak256Transcript::from_proof((), proof.as_slice());
        //     Pcs::verify(
        //         &vp,
        //         &Pcs::read_commitment(&vp, &mut transcript).unwrap(),
        //         &<Pcs as PolynomialCommitmentScheme<Fr>>::Polynomial::squeeze_point(m, &mut transcript),

        //         // Use the correct method to read the field element
        //         &transcript.read_field_element().unwrap(),
        //         &mut transcript,
        //     )
        // };
        // assert_eq!(result, Ok(()));

    }
}