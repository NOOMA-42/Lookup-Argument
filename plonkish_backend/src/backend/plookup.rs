use std::{fmt::Debug, hash::Hash, marker::PhantomData};
use halo2_curves::ff::WithSmallOrderMulGroup;
use crate::{
    poly::univariate::UnivariatePolynomial,
    pcs::PolynomialCommitmentScheme,
    util::{
        arithmetic::PrimeField,
        Deserialize, DeserializeOwned, Serialize,
        transcript::{InMemoryTranscript, TranscriptRead, TranscriptWrite},
    },
    Error,
};

pub mod preprocessor;
pub mod prover;
pub mod verifier;
pub mod util;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PlookupProverParam <F, Pcs>
where
    F: PrimeField,
    Pcs: PolynomialCommitmentScheme<F>,
{
    pcs: Pcs::ProverParam,
    g: F,
    table: Vec<F>,
    lookup: Vec<F>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PlookupVerifierParam<F, Pcs>
where
    F: PrimeField,
    Pcs: PolynomialCommitmentScheme<F>,
{
    pcs: Pcs::VerifierParam,
    g: F,
    table: Vec<F>,
}

#[derive(Clone, Debug)]
pub struct PlookupInfo<F> {
    k: u32,
    table: Vec<F>,
    lookup: Vec<F>,
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
        preprocessor::preprocess(param, info)
    }

    fn prove(
        pp: PlookupProverParam<F, Pcs>,
        transcript: &mut (impl TranscriptWrite<Pcs::CommitmentChunk, F> + InMemoryTranscript),
    ) -> Result<(), Error> {
        prover::prove(pp, transcript)
    }

    fn verify(
        vp: PlookupVerifierParam<F, Pcs>,
        transcript: &mut (impl TranscriptRead<Pcs::CommitmentChunk, F> + InMemoryTranscript),
    ) -> Result<(), Error> {
        verifier::verify(vp, transcript)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use halo2_curves::bn256::{Bn256, Fr};
    use crate::{
        pcs::univariate::UnivariateKzg,
        util::{
            test::std_rng,
            transcript::Keccak256Transcript,
        },
    };

    type Pcs = UnivariateKzg<Bn256>;
    type Pb = Plookup<Fr, Pcs>;

    #[test]
    fn test_e2e() {
        let k = 2;
        let n = 1 << k;
        let lookup = vec![Fr::one(), Fr::one(), Fr::from(2)];
        let table = vec![Fr::one(), Fr::from(2), Fr::from(3), Fr::from(4)];
        let info = PlookupInfo{k, table, lookup};
        let mut rng = std_rng();

        // Setup
        let (pp, vp) = {
            let param = Pcs::setup(n*4, 1, &mut rng).unwrap();
            Pb::preprocess(&param, &info).unwrap()
        };

        let mut transcript = Keccak256Transcript::new(());
        // Prove
        Pb::prove(pp, &mut transcript).unwrap();
        let proof = transcript.into_proof();
        let mut transcript = Keccak256Transcript::from_proof((), proof.as_slice());
        // Verify
        Pb::verify(vp, &mut transcript).unwrap();
    }
}
