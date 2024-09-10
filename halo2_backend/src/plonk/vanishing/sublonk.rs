use crate::arithmetic::CurveAffine;
use crate::plonk::vanishing::verifier::{Committed, Constructed};
use crate::plonk::Error;
use crate::poly::EvaluationDomain;
use crate::transcript::{read_n_points, EncodedChallenge, TranscriptRead};

impl<C: CurveAffine> Committed<C> {
    pub(in crate::plonk) fn read_commitments_after_y_by_domain<
        E: EncodedChallenge<C>,
        T: TranscriptRead<C, E>,
    >(
        self,
        domain: &EvaluationDomain<C::Scalar>,
        transcript: &mut T,
    ) -> Result<Constructed<C>, Error> {
        // Obtain a commitment to h(X) in the form of multiple pieces of degree n - 1
        let h_commitments = read_n_points(transcript, domain.get_quotient_poly_degree())?;

        Ok(Constructed {
            h_commitments,
            random_poly_commitment: self.random_poly_commitment,
        })
    }
}