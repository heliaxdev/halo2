use crate::{
    poseidontranscript::{
        POSEIDON_PREFIX_CHALLENGE, POSEIDON_PREFIX_POINT, POSEIDON_PREFIX_SCALAR,
    },
    transcript::{Transcript, TranscriptInstructions},
};
use group::{
    ff::{Field, PrimeField},
    Curve,
};
use halo2_gadgets::endoscale::EndoscaleInstructions;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, Error, VerifyingKey},
    poly::commitment::{Blind, Params},
    transcript::{EncodedChallenge, TranscriptRead},
};
use pasta_curves::vesta;
use std::marker::PhantomData;

/// Accumulator verifier
pub struct Verifier<E, EndoscaleChip, TranscriptChip, TR>
where
    E: EncodedChallenge<vesta::Affine>,
    EndoscaleChip: EndoscaleInstructions<vesta::Affine>,
    TranscriptChip: TranscriptInstructions<vesta::Affine>,
    TR: TranscriptRead<vesta::Affine, E> + Clone,
{
    vk: VerifyingKey<vesta::Affine>,
    transcript: Transcript<vesta::Affine, TranscriptChip>,
    endoscale_chip: EndoscaleChip,
    fixed_bases: Vec<EndoscaleChip::FixedBases>,
    _marker: PhantomData<(E, TR)>,
}

impl<
        E: EncodedChallenge<vesta::Affine>,
        EndoscaleChip: EndoscaleInstructions<vesta::Affine>,
        TranscriptChip: TranscriptInstructions<vesta::Affine>,
        TR: TranscriptRead<vesta::Affine, E> + Clone,
    > Verifier<E, EndoscaleChip, TranscriptChip, TR>
{
    pub fn new(
        vk: VerifyingKey<vesta::Affine>,
        transcript_chip: TranscriptChip,
        endoscale_chip: EndoscaleChip,
        fixed_bases: Vec<EndoscaleChip::FixedBases>,
    ) -> Self {
        Self {
            vk,
            transcript: Transcript::new(transcript_chip),
            endoscale_chip,
            fixed_bases,
            _marker: PhantomData,
        }
    }

    pub fn verify_proof(
        &mut self,
        params: &Params<vesta::Affine>,
        mut layouter: impl Layouter<vesta::Base>,
        mut proof: Value<TR>,
        pre_instances: &[&[vesta::Scalar]],
        column: Column<Advice>,
    ) -> Result<(), Error> {
        // Check that instances matches the expected number of instance columns
        if pre_instances.len() != self.vk.cs().num_instance_columns() {
            return Err(Error::InvalidInstances);
        }

        // Check instance_commitments construction out of circuit
        // In Taiga, the instances of resource logic are open to public in practice.
        let instance_commitments: Vec<vesta::Affine> = pre_instances
            .iter()
            .map(|instance| {
                let mut poly = instance.to_vec();
                poly.resize(params.n() as usize, vesta::Scalar::ZERO);
                let poly = self.vk.get_domain().lagrange_from_vec(poly);

                params.commit_lagrange(&poly, Blind::default()).to_affine()
            })
            .collect();

        // TODO: move the constants to transcript
        let prefix_challenge = layouter.assign_region(
            || "load prefix_challenge",
            |mut region| {
                region.assign_advice_from_constant(
                    || "load constant",
                    column,
                    0,
                    POSEIDON_PREFIX_CHALLENGE.clone(),
                )
            },
        )?;
        let prefix_point = layouter.assign_region(
            || "load prefix_point",
            |mut region| {
                region.assign_advice_from_constant(
                    || "load constant",
                    column,
                    0,
                    POSEIDON_PREFIX_POINT.clone(),
                )
            },
        )?;
        let prefix_scalar = layouter.assign_region(
            || "load prefix_scalar",
            |mut region| {
                region.assign_advice_from_constant(
                    || "load constant",
                    column,
                    0,
                    POSEIDON_PREFIX_SCALAR.clone(),
                )
            },
        )?;

        // TODO: Compress verifying key

        // Hash verification key into transcript
        self.transcript.common_scalar(
            layouter.namespace(|| "vk"),
            prefix_challenge.clone(),
            Value::known(self.vk.transcript_repr()),
        )?;

        // Hash the instance commitments into the transcript
        for commitment in instance_commitments {
            self.transcript.common_point(
                layouter.namespace(|| "instance commitments"),
                prefix_point.clone(),
                Value::known(commitment),
            )?;
        }

        // Hash the prover's advice commitments into the transcript
        let cs = self.vk.cs();
        for _ in 0..cs.num_advice_columns() {
            let advice = proof.map(|p| p.read_point().unwrap());
            self.transcript.common_point(
                layouter.namespace(|| "advice commitments"),
                prefix_point.clone(),
                advice,
            )?;
        }

        // Sample theta challenge for keeping lookup columns linearly independent
        let theta = self
            .transcript
            .squeeze_challenge(layouter.namespace(|| "theta challenge"), prefix_challenge);

        // Hash each lookup permuted commitment
        let lookups_permuted = (0..self.vk.cs().get_lookups_num())
            .map(|_| {
                let advice = proof.map(|p| p.read_point().unwrap());
                let permuted_input_commitment = self.transcript.common_point(
                    layouter.namespace(|| "advice permuted_input_commitment"),
                    prefix_point.clone(),
                    advice,
                )?;
                let advice = proof.map(|p| p.read_point().unwrap());
                let permuted_table_commitment = self.transcript.common_point(
                    layouter.namespace(|| "advice permuted_table_commitment"),
                    prefix_point.clone(),
                    advice,
                )?;
                Ok((permuted_input_commitment, permuted_table_commitment))
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Sample beta challenge
        let beta = self
            .transcript
            .squeeze_challenge(layouter.namespace(|| "beta challenge"), prefix_challenge);

        // Sample gamma challenge
        let gamma = self
            .transcript
            .squeeze_challenge(layouter.namespace(|| "gamma challenge"), prefix_challenge);

        // Hash each permutation product commitment
        let chunk_len = self.vk.get_cs_degree() - 2;
        let permutations_committed = self
            .vk
            .cs()
            .permutation()
            .get_columns()
            .chunks(chunk_len)
            .map(|_| {
                let advice = proof.map(|p| p.read_point().unwrap());
                self.transcript.common_point(
                    layouter.namespace(|| "advice permutation_product_commitments"),
                    prefix_point.clone(),
                    advice,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Hash each lookup product commitment
        let lookups_committed = lookups_permuted
            .into_iter()
            .map(|lookups| {
                let advice = proof.map(|p| p.read_point().unwrap());
                let product_commitment = self.transcript.common_point(
                    layouter.namespace(|| "advice permutation_product_commitments"),
                    prefix_point.clone(),
                    advice,
                )?;
                Ok((lookups.0, lookups.1, product_commitment))
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Hash vanishing commitments
        let advice = proof.map(|p| p.read_point().unwrap());
        let vanishing = self.transcript.common_point(
            layouter.namespace(|| "advice vanishing"),
            prefix_point.clone(),
            advice,
        )?;

        // Sample y challenge, which keeps the gates linearly independent.
        let y = self
            .transcript
            .squeeze_challenge(layouter.namespace(|| "y challenge"), prefix_challenge);

        let vanishing = {
            let h_commitments = (0..self.vk.get_domain().get_quotient_poly_degree())
                .map(|_| {
                    let advice = proof.map(|p| p.read_point().unwrap());
                    self.transcript.common_point(
                        layouter.namespace(|| "advice permuted_input_commitment"),
                        prefix_point.clone(),
                        advice,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            (h_commitments, vanishing)
        };

        // Sample x challenge, which is used to ensure the circuit is satisfied with high probability.
        let x = self
            .transcript
            .squeeze_challenge(layouter.namespace(|| "x challenge"), prefix_challenge)?;

        // Read instance_queries
        let instance_evals = (0..self.vk.cs().get_instance_queries_num())
            .map(|_| {
                let advice = proof.map(|p| p.read_scalar().unwrap());
                self.transcript.common_scalar(
                    layouter.namespace(|| "advice instance_evals"),
                    prefix_scalar.clone(),
                    advice,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Read advice_queries
        let advice_evals = (0..self.vk.cs().get_advice_queries_num())
            .map(|_| {
                let advice = proof.map(|p| p.read_scalar().unwrap());
                self.transcript.common_scalar(
                    layouter.namespace(|| "advice advice_evals"),
                    prefix_scalar.clone(),
                    advice,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Read fixed_queries
        let fixed_evals = (0..self.vk.cs().get_fixed_queries_num())
            .map(|_| {
                let advice = proof.map(|p| p.read_scalar().unwrap());
                self.transcript.common_scalar(
                    layouter.namespace(|| "advice fixed_evals"),
                    prefix_scalar.clone(),
                    advice,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Read vanishing random_eval
        let advice = proof.map(|p| p.read_scalar().unwrap());
        let vanishing_random_eval = self.transcript.common_scalar(
            layouter.namespace(|| "advice vanishing_random_eval"),
            prefix_scalar.clone(),
            advice,
        )?;

        // Read permutations_common
        let permutations_common = self
            .vk
            .permutation()
            .commitments()
            .iter()
            .map(|_| {
                let advice = proof.map(|p| p.read_scalar().unwrap());
                self.transcript.common_scalar(
                    layouter.namespace(|| "advice permutations_common"),
                    prefix_scalar.clone(),
                    advice,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Read permutations_evaluated
        let permutations_evaluated = {
            let mut sets = vec![];

            let mut iter = permutations_committed.into_iter();

            while let Some(permutation_product_commitment) = iter.next() {
                let advice = proof.map(|p| p.read_scalar().unwrap());
                let permutation_product_eval = self.transcript.common_scalar(
                    layouter.namespace(|| "advice permutation_product_eval"),
                    prefix_scalar.clone(),
                    advice,
                )?;
                let advice = proof.map(|p| p.read_scalar().unwrap());
                let permutation_product_next_eval = self.transcript.common_scalar(
                    layouter.namespace(|| "advice permutation_product_next_eval"),
                    prefix_scalar.clone(),
                    advice,
                )?;
                let permutation_product_last_eval = if iter.len() > 0 {
                    let advice = proof.map(|p| p.read_scalar().unwrap());
                    let permutation_product_next_eval = self.transcript.common_scalar(
                        layouter.namespace(|| "advice permutation_product_next_eval"),
                        prefix_scalar.clone(),
                        advice,
                    )?;
                    Some(permutation_product_next_eval)
                } else {
                    None
                };

                sets.push((
                    permutation_product_commitment,
                    permutation_product_eval,
                    permutation_product_next_eval,
                    permutation_product_last_eval,
                ));
            }
            sets
        };

        // Read lookups_evaluated
        let lookups_evaluated = lookups_committed
            .into_iter()
            .map(|lookup| {
                let advice = proof.map(|p| p.read_scalar().unwrap());
                let product_eval = self.transcript.common_scalar(
                    layouter.namespace(|| "advice product_eval"),
                    prefix_scalar.clone(),
                    advice,
                )?;
                let advice = proof.map(|p| p.read_scalar().unwrap());
                let product_next_eval = self.transcript.common_scalar(
                    layouter.namespace(|| "advice product_next_eval"),
                    prefix_scalar.clone(),
                    advice,
                )?;
                let advice = proof.map(|p| p.read_scalar().unwrap());
                let permuted_input_eval = self.transcript.common_scalar(
                    layouter.namespace(|| "advice permuted_input_eval"),
                    prefix_scalar.clone(),
                    advice,
                )?;
                let advice = proof.map(|p| p.read_scalar().unwrap());
                let permuted_input_inv_eval = self.transcript.common_scalar(
                    layouter.namespace(|| "advice permuted_input_inv_eval"),
                    prefix_scalar.clone(),
                    advice,
                )?;
                let advice = proof.map(|p| p.read_scalar().unwrap());
                let permuted_table_eval = self.transcript.common_scalar(
                    layouter.namespace(|| "advice permuted_table_eval"),
                    prefix_scalar.clone(),
                    advice,
                )?;
                Ok((
                    lookup,
                    product_eval,
                    product_next_eval,
                    permuted_input_eval,
                    permuted_input_inv_eval,
                    permuted_table_eval,
                ))
            })
            .collect::<Result<Vec<_>, _>>()?;

        // TODO: vanishing check, Compute the expected value of h(x)
        // Defer the non-native arithmetic to the next layer.

        // TODO: init queries
        // let queries = {};

        // TODO: check polynomial commitments open(multi-open) to the correct values

        // Old accumulator
        // let acc = A::read_instance(instances);
        // // Proof of previous recursive circuit
        // let new_instance = A::read_instance(instances);
        // // FIXME: We can calculate this ourselves
        // let new_acc = A::read_new_acc(instances);

        // Ok((
        //     A::check_new_acc(&[acc, new_instance], new_acc, is_base_case),
        //     new_acc,
        // ))

        Ok(())
    }
}

/// Converts from vesta::Scalar to vesta::Base (aka $x \pmod{r_\mathbb{P}}$).
///
/// This requires no modular reduction because vesta' Scalar field is smaller than its
/// Base field.
fn mod_r_p(x: vesta::Scalar) -> vesta::Base {
    vesta::Base::from_repr(x.to_repr()).unwrap()
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use halo2_gadgets::{
        ecc::EccInstructions,
        endoscale::EndoscaleInstructions,
        poseidon::{
            primitives::{Absorbing, Domain, Spec},
            PaddedWord, PoseidonSpongeInstructions, Sponge,
        },
        utilities::{bitstring::BitstringInstructions, UtilitiesInstructions},
    };
    use halo2_proofs::{
        arithmetic::{CurveAffine, Field},
        circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        pasta::{
            group::ff::{PrimeField, PrimeFieldBits},
            EpAffine, EqAffine,
        },
        plonk::{
            create_proof, keygen_pk, keygen_vk, Circuit, ConstraintSystem, Error, VerifyingKey,
        },
        poly::commitment::Params,
        transcript::{
            self, Blake2bRead, Blake2bWrite, Challenge255, EncodedChallenge, TranscriptRead,
        },
    };
    use rand_core::OsRng;

    use super::super::Instance;
    use super::Verifier;
    use crate::{
        accumulator::{Accumulator, SplitAccumulator},
        transcript::{DuplexInstructions, TranscriptInstructions},
    };

    #[derive(Clone, Copy)]
    struct BaseCircuit;

    impl<F: Field> Circuit<F> for BaseCircuit {
        type Config = ();

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            *self
        }

        fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {}

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            Ok(())
        }
    }

    struct EndoscaleChip<C: CurveAffine>(PhantomData<C>);
    impl<C: CurveAffine> EndoscaleInstructions<C> for EndoscaleChip<C>
    where
        C::Base: PrimeFieldBits,
    {
        type NonIdentityPoint = ();

        type Bitstring = ();

        type FixedBases = ();

        const MAX_BITSTRING_LENGTH: usize = 0;

        const NUM_FIXED_BASES: usize = 0;

        fn fixed_bases(&self) -> Vec<Self::FixedBases> {
            vec![]
        }

        fn witness_bitstring(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            bits: &[Value<bool>],
            for_base: bool,
        ) -> Result<Vec<Self::Bitstring>, Error> {
            todo!()
        }

        fn endoscale_fixed_base(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            bitstring: Vec<Self::Bitstring>,
            bases: Vec<Self::FixedBases>,
        ) -> Result<Vec<Self::NonIdentityPoint>, Error> {
            todo!()
        }

        fn endoscale_var_base(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            bitstring: Vec<Self::Bitstring>,
            bases: Vec<Self::NonIdentityPoint>,
        ) -> Result<Vec<Self::NonIdentityPoint>, Error> {
            todo!()
        }

        fn compute_endoscalar(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            bitstring: &Self::Bitstring,
        ) -> Result<
            halo2_proofs::circuit::AssignedCell<
                halo2_proofs::plonk::Assigned<<C as CurveAffine>::Base>,
                <C as CurveAffine>::Base,
            >,
            Error,
        > {
            todo!()
        }

        fn constrain_bitstring(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            bitstring: &Self::Bitstring,
            pub_input_rows: Vec<usize>,
        ) -> Result<(), Error> {
            todo!()
        }
    }

    #[derive(PartialEq, Eq, Debug, Clone)]
    struct TranscriptChip<
        F: Field,
        PoseidonChip: PoseidonSpongeInstructions<F, S, D, T, RATE>,
        S: Spec<F, T, RATE>,
        D: Domain<F, RATE>,
        const T: usize,
        const RATE: usize,
    > {
        poseidon_sponge: Sponge<F, PoseidonChip, S, Absorbing<PaddedWord<F>, RATE>, D, T, RATE>,
    }
    impl<F: PrimeField> Chip<F> for TranscriptChip {
        type Config = ();

        type Loaded = ();

        fn config(&self) -> &Self::Config {
            todo!()
        }

        fn loaded(&self) -> &Self::Loaded {
            todo!()
        }
    }
    impl<F: PrimeField> DuplexInstructions<F> for TranscriptChip {
        fn absorb(
            &mut self,
            mut layouter: impl Layouter<F>,
            value: AssignedCell<F, F>,
        ) -> Result<(), Error> {
            self.poseidon_sponge
                .absorb(layouter.namespace(|| format!("sponge absorb")), value)?;

            Ok(())
        }

        fn squeeze(&mut self, mut layouter: impl Layouter<F>) -> Result<AssignedCell<F, F>, Error> {
            let mut poseidon_sponge = self
                .poseidon_sponge
                .finish_absorbing(layouter.namespace(|| "sponge finish absorb"))?;
            let output = poseidon_sponge.squeeze(layouter.namespace(|| "sponge squeeze"))?;
            self.poseidon_sponge =
                poseidon_sponge.finish_squeezing(layouter.namespace(|| "sponge finish squeeze"))?;
            Ok(output)
        }
    }
    impl<F: PrimeField> BitstringInstructions<F> for TranscriptChip {
        fn constrain(
            &self,
            layouter: impl Layouter<F>,
            witnessed: &AssignedCell<F, F>,
            num_bits: usize,
        ) -> Result<halo2_gadgets::utilities::RangeConstrained<F, AssignedCell<F, F>>, Error>
        {
            todo!()
        }

        fn extract_bitrange(
            &self,
            layouter: impl Layouter<F>,
            witnessed: &AssignedCell<F, F>,
            range: std::ops::Range<usize>,
        ) -> Result<halo2_gadgets::utilities::RangeConstrained<F, AssignedCell<F, F>>, Error>
        {
            todo!()
        }
    }
    impl<C: CurveAffine> TranscriptInstructions<C> for TranscriptChip where C::Base: PrimeFieldBits {}
    impl<F: PrimeField> UtilitiesInstructions<F> for TranscriptChip {
        type Var = AssignedCell<F, F>;
    }

    #[derive(PartialEq, Clone, Eq, Debug)]
    struct FixedPoints;
    impl<C: CurveAffine> halo2_gadgets::ecc::FixedPoints<C> for FixedPoints {
        type FullScalar = ();

        type ShortScalar = ();

        type Base = ();
    }
    impl<C: CurveAffine> EccInstructions<C> for TranscriptChip
    where
        C::Base: PrimeFieldBits,
    {
        type ScalarVar = ();
        type ScalarFixed = ();
        type ScalarFixedShort = ();
        type Point = ();
        type NonIdentityPoint = ();
        type X = ();
        type FixedPoints = FixedPoints;

        fn constrain_equal(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            a: &Self::Point,
            b: &Self::Point,
        ) -> Result<(), Error> {
            Ok(())
        }

        fn witness_point(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            value: Value<C>,
        ) -> Result<Self::Point, Error> {
            Ok(())
        }

        fn witness_point_non_id(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            value: Value<C>,
        ) -> Result<Self::NonIdentityPoint, Error> {
            Ok(())
        }

        fn witness_scalar_var(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            value: Value<<C>::Scalar>,
        ) -> Result<Self::ScalarVar, Error> {
            Ok(())
        }

        fn witness_scalar_fixed(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            value: Value<<C>::Scalar>,
        ) -> Result<Self::ScalarFixed, Error> {
            Ok(())
        }

        fn scalar_fixed_from_signed_short(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            magnitude_sign: (Self::Var, Self::Var),
        ) -> Result<Self::ScalarFixedShort, Error> {
            Ok(())
        }

        fn extract_p<Point: Into<Self::Point> + Clone>(point: &Point) -> Self::X {
            ()
        }

        fn double(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            a: &Self::NonIdentityPoint,
        ) -> Result<Self::NonIdentityPoint, Error> {
            Ok(())
        }

        fn add_incomplete(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            a: &Self::NonIdentityPoint,
            b: &Self::NonIdentityPoint,
        ) -> Result<Self::NonIdentityPoint, Error> {
            Ok(())
        }

        fn add<A: Into<Self::Point> + Clone, B: Into<Self::Point> + Clone>(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            a: &A,
            b: &B,
        ) -> Result<Self::Point, Error> {
            Ok(())
        }

        fn mul(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            scalar: &Self::ScalarVar,
            base: &Self::NonIdentityPoint,
        ) -> Result<(Self::Point, Self::ScalarVar), Error> {
            Ok(((), ()))
        }

        fn mul_fixed(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            scalar: &Self::ScalarFixed,
            base: &<Self::FixedPoints as halo2_gadgets::ecc::FixedPoints<C>>::FullScalar,
        ) -> Result<(Self::Point, Self::ScalarFixed), Error> {
            Ok(((), ()))
        }

        fn mul_fixed_short(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            scalar: &Self::ScalarFixedShort,
            base: &<Self::FixedPoints as halo2_gadgets::ecc::FixedPoints<C>>::ShortScalar,
        ) -> Result<(Self::Point, Self::ScalarFixedShort), Error> {
            Ok(((), ()))
        }

        fn mul_fixed_base_field_elem(
            &self,
            layouter: &mut impl Layouter<<C as CurveAffine>::Base>,
            base_field_elem: Self::Var,
            base: &<Self::FixedPoints as halo2_gadgets::ecc::FixedPoints<C>>::Base,
        ) -> Result<Self::Point, Error> {
            Ok(())
        }
    }

    fn transcript_chip<C: CurveAffine, T: TranscriptInstructions<C>>() -> T {
        todo!()
    }

    fn endoscale_chip<C: CurveAffine, E: EndoscaleInstructions<C>>() -> E
    where
        C::Base: PrimeFieldBits,
    {
        todo!()
    }

    #[derive(Clone)]
    struct VerifierCircuit<
        'a,
        C: CurveAffine,
        E: EncodedChallenge<C>,
        TR: TranscriptRead<C, E> + Clone,
    >
    where
        C::Base: PrimeFieldBits,
    {
        vk: VerifyingKey<C>,
        proof: Value<TR>,
        instances: &'a [Instance],
        _marker: PhantomData<(C, E)>,
    }

    impl<'a, C: CurveAffine, E: EncodedChallenge<C>, TR: TranscriptRead<C, E> + Clone>
        Circuit<C::Base> for VerifierCircuit<'a, C, E, TR>
    where
        C::Base: PrimeFieldBits,
    {
        type Config = ();

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                vk: self.vk.clone(),
                proof: self.proof.clone(),
                instances: &self.instances,
                _marker: PhantomData,
            }
        }

        fn configure(_meta: &mut ConstraintSystem<C::Base>) -> Self::Config {}

        fn synthesize(
            &self,
            _config: Self::Config,
            mut layouter: impl Layouter<C::Base>,
        ) -> Result<(), Error> {
            let mut verifier = Verifier::new(
                self.vk.clone(),
                TranscriptChip,
                EndoscaleChip(PhantomData),
                EndoscaleChip::<C>(PhantomData).fixed_bases(),
            );

            // FIXME: We need to output `acc` from `synthesize()`
            let (_, acc) = verifier.verify_proof::<SplitAccumulator<C>>(
                layouter.namespace(|| "instance 0"),
                self.proof.clone(),
                self.instances,
                Value::known(false),
            )?;

            Ok(())
        }
    }

    #[derive(Clone)]
    struct BaseVerifierCircuit<
        'a,
        C: CurveAffine,
        E: EncodedChallenge<C>,
        TR: TranscriptRead<C, E> + Clone,
    >
    where
        C::Base: PrimeFieldBits,
    {
        vk: VerifyingKey<C>,
        proof: Value<TR>,
        instances: &'a [Instance],
        _marker: PhantomData<(C, E)>,
    }

    impl<'a, C: CurveAffine, E: EncodedChallenge<C>, TR: TranscriptRead<C, E> + Clone>
        Circuit<C::Base> for BaseVerifierCircuit<'a, C, E, TR>
    where
        C::Base: PrimeFieldBits,
    {
        type Config = ();

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                vk: self.vk.clone(),
                proof: self.proof.clone(),
                instances: &self.instances,
                _marker: PhantomData,
            }
        }

        fn configure(_meta: &mut ConstraintSystem<C::Base>) -> Self::Config {}

        fn synthesize(
            &self,
            _config: Self::Config,
            mut layouter: impl Layouter<C::Base>,
        ) -> Result<(), Error> {
            let mut verifier = Verifier::new(
                self.vk.clone(),
                TranscriptChip,
                EndoscaleChip(PhantomData),
                EndoscaleChip::<C>(PhantomData).fixed_bases(),
            );

            // FIXME: We need to output `acc` from `synthesize()`
            let (_, acc) = verifier.verify_proof::<SplitAccumulator<C>>(
                layouter.namespace(|| "instance 0"),
                self.proof.clone(),
                self.instances,
                Value::known(true),
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_verify_gadget() {
        let params: Params<EqAffine> = Params::new(3);
        let vk = keygen_vk(&params, &BaseCircuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk.clone(), &BaseCircuit).expect("keygen_pk should not fail");
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

        create_proof(&params, &pk, &[BaseCircuit], &[&[]], OsRng, &mut transcript).unwrap();
        let proof = transcript.finalize();
        let mut proof = Blake2bRead::init(&proof[..]);

        // FIXME: Calculate acc and new_acc for base case

        let base_verifier = BaseVerifierCircuit::<'_, EqAffine, Challenge255<EqAffine>, _> {
            vk,
            proof: Value::known(proof),
            instances: &[],
            _marker: PhantomData,
        };

        let k = 13;
        let prover = MockProver::run(k, &base_verifier, vec![]).unwrap();
        prover.assert_satisfied();

        let params: Params<EqAffine> = Params::new(3);
        let vk = keygen_vk(&params, &BaseCircuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk.clone(), &BaseCircuit).expect("keygen_pk should not fail");
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

        create_proof(&params, &pk, &[BaseCircuit], &[&[]], OsRng, &mut transcript).unwrap();
        let proof = transcript.finalize();
        let mut proof = Blake2bRead::init(&proof[..]);

        // FIXME: Calculate acc and new_acc for recursive case

        let verifier = VerifierCircuit::<'_, EqAffine, Challenge255<EqAffine>, _> {
            vk,
            proof: Value::known(proof),
            instances: &[],
            _marker: PhantomData,
        };

        let k = 13;
        let prover = MockProver::run(k, &verifier, vec![]).unwrap();
        prover.assert_satisfied();
    }
}
