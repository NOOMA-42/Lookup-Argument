use halo2_curves::ff::WithSmallOrderMulGroup;
use crate::{
    pcs::{PolynomialCommitmentScheme,Evaluation},
    poly::univariate::UnivariatePolynomial,
    util::{
        arithmetic::PrimeField,
        transcript::{TranscriptRead,InMemoryTranscript},
    },
    Error,
};
use super::{
    PlookupVerifierParam,
    util::aggregate_field,
};

pub(super) fn verify<
    F: PrimeField + WithSmallOrderMulGroup<3>, 
    Pcs: PolynomialCommitmentScheme<F, Polynomial = UnivariatePolynomial<F>>,
>(
    vp: PlookupVerifierParam<F, Pcs>,
    transcript: &mut (impl TranscriptRead<Pcs::CommitmentChunk, F> + InMemoryTranscript),
) -> Result<(), Error> {
    let f_comm = Pcs::read_commitment(&vp.pcs, transcript)?;
    let h1_comm = Pcs::read_commitment(&vp.pcs, transcript)?;
    let h2_comm = Pcs::read_commitment(&vp.pcs, transcript)?;
    let mut challenges: Vec<F> = Vec::with_capacity(2);
    challenges.extend(transcript.squeeze_challenges(2));
    let beta = &challenges[0];
    let gamma = &challenges[1];
    let z_comm = Pcs::read_commitment(&vp.pcs, transcript)?;
    let delta = &transcript.squeeze_challenge();
    let q_comm = Pcs::read_commitment(&vp.pcs, transcript)?;
    let zeta = &transcript.squeeze_challenge();
    // [f_eval, h1_eval, h2_eval, z_eval]
    let evals = transcript.read_field_elements(4)?;
    // [h1_g_eval, h2_g_eval, z_g_eval]
    let g_evals = transcript.read_field_elements(3)?;
    let q_eval = compute_quotient_polynomial_eval(
        &vp.g, beta, gamma, delta, zeta, &vp.table, 
        &evals[0], &evals[1], &evals[2], &evals[3],
        &g_evals[0], &g_evals[1], &g_evals[2]
    );
    let batch_comms = [&f_comm, &h1_comm, &h2_comm, &z_comm, &q_comm];
    let batch_points = [*zeta, vp.g*zeta];
    let batch_evals = [
        Evaluation::new(0, 0, evals[0]),
        Evaluation::new(1, 0, evals[1]),
        Evaluation::new(2, 0, evals[2]),
        Evaluation::new(3, 0, evals[3]),
        Evaluation::new(4, 0, q_eval),
        Evaluation::new(1, 1, g_evals[0]),
        Evaluation::new(2, 1, g_evals[1]),
        Evaluation::new(3, 1, g_evals[2]),
    ];
    Pcs::batch_verify(&vp.pcs, batch_comms, &batch_points, &batch_evals, transcript)?;
    Ok(())
}

fn compute_quotient_polynomial_eval<F: PrimeField+WithSmallOrderMulGroup<3>>(
    g: &F,
    beta: &F,
    gamma: &F,
    delta: &F,
    zeta: &F,
    t: &Vec<F>,
    f_eval: &F,
    h1_eval: &F,
    h2_eval: &F,
    z_eval: &F,
    h1_g_eval: &F,
    h2_g_eval: &F,
    z_g_eval: &F,
) -> F {
    let n = t.len();
    let l0_poly = {
        let mut values = vec![F::ZERO; n];
        values[0] = F::ONE;
        UnivariatePolynomial::lagrange(values).ifft()
    };
    let l0_eval = l0_poly.evaluate(zeta);
    let ln_poly = {
        let mut values = vec![F::ZERO; n];
        values[n-1] = F::ONE;
        UnivariatePolynomial::lagrange(values).ifft()
    };
    let ln_eval = ln_poly.evaluate(zeta);
    let a = l0_eval * (*z_eval - F::ONE);
    let b = {
        let t_poly = UnivariatePolynomial::lagrange(t.clone()).ifft();
        let t_eval = t_poly.evaluate(zeta);
        let t_g_eval = t_poly.evaluate(&(*g*zeta));
        let front = *zeta - F::invert(g).unwrap();
        let beta_plus_1 = F::ONE + beta;
        let lhs = *z_eval * beta_plus_1 * (*f_eval + *gamma) *
            (t_eval + t_g_eval * beta + beta_plus_1 * gamma);
        let rhs = *z_g_eval * (*h1_eval + *h1_g_eval * beta + beta_plus_1 * gamma) *
            (*h2_eval + *h2_g_eval * beta + beta_plus_1 * gamma);
        front * (lhs - rhs)
    };
    let c = ln_eval * (*h1_eval - h2_g_eval);
    let d = ln_eval * (*z_eval - F::ONE);
    let vanish = { // x^n - 1
        let mut coeffs = vec![F::ZERO; n+1];
        coeffs[0] = -F::ONE;
        coeffs[n] = F::ONE;
        UnivariatePolynomial::monomial(coeffs)
    };
    let divisor_inv = F::invert(&vanish.evaluate(zeta)).unwrap();
    aggregate_field(delta, vec![&a, &b, &c, &d]) * divisor_inv
}
