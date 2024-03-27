use std::marker::PhantomData;

use halo2_gadgets::{
    ecc::{EccInstructions, Point},
    utilities::{bitstring::BitstringInstructions, RangeConstrained},
};
use halo2_proofs::{
    arithmetic::CurveAffine,
    circuit::{AssignedCell, Layouter, Value, Chip},
    pasta::group::ff::PrimeField,
    plonk::{Column, Error, Advice},
};

pub trait DuplexInstructions<F: PrimeField> {
    fn absorb(
        &mut self,
        layouter: &mut impl Layouter<F>,
        value: AssignedCell<F, F>,
    ) -> Result<(), Error>;
    fn squeeze(&mut self, layouter: &mut impl Layouter<F>) -> Result<AssignedCell<F, F>, Error>;
}

pub trait TranscriptInstructions<C: CurveAffine>:
    BitstringInstructions<C::Base> + DuplexInstructions<C::Base> + EccInstructions<C>
{
}

#[derive(Clone, Debug)]
pub struct TranscriptChip<F: PrimeField> {
    config: TranscriptConfig<F>,
}

impl<F: PrimeField> Chip<F> for TranscriptChip<F> {
    type Config = ();

    type Loaded = ();

    fn config(&self) -> &Self::Config {
        todo!()
    }

    fn loaded(&self) -> &Self::Loaded {
        todo!()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TranscriptConfig<F: PrimeField> {
    advices: [Column<Advice>; 10],
    _marker: PhantomData<F>,
}

/// A Transcript gadget
pub struct Transcript<F: PrimeField>
{
    transcript_chip: TranscriptChip<F>,
}

impl<C, TranscriptChip> Transcript<C, TranscriptChip>
where
    C: CurveAffine,
    TranscriptChip: TranscriptInstructions<C>,
{
    pub fn new(transcript_chip: TranscriptChip) -> Self {
        Self {
            transcript_chip,
            _marker: PhantomData,
        }
    }

    /// Hashes a point into the transcript.
    pub fn common_point(
        &mut self,
        mut layouter: impl Layouter<C::Base>,
        prefix_point: AssignedCell<C::Base, C::Base>,
        point: Value<C>,
    ) -> Result<Point<C, TranscriptChip>, Error> {
        // Witness point
        let point = Point::new(
            self.transcript_chip.clone(),
            layouter.namespace(|| "witness points"),
            point,
        )?;

        // absorb POSEIDON_PREFIX_POINT
        self.transcript_chip
            .absorb(&mut layouter, prefix_point.clone())?;
        self.transcript_chip.absorb(&mut layouter, prefix_point)?;

        // absorb x and y
        self.transcript_chip.absorb(&mut layouter, point.x())?;
        self.transcript_chip.absorb(&mut layouter, point.y())?;

        Ok(point)
    }

    /// Reads a scalar field element from the transcript.
    ///
    /// This instruction does the following steps:
    /// - Constrains the next sequence of proof bits to be the representation of a scalar
    ///   field element.
    /// - Assigns the scalar field element into the circuit.
    /// - Updates the transcript's internal state with this scalar field element.
    /// - Returns the assigned scalar field element.
    pub fn common_scalar(
        &mut self,
        mut layouter: impl Layouter<C::Base>,
        prefix_scalar: AssignedCell<C::Base, C::Base>,
        scalar: Value<C::Scalar>,
    ) -> Result<(), Error> {
        // absorb POSEIDON_PREFIX_SCALAR
        self.transcript_chip.absorb(&mut layouter, prefix_scalar)?;
        // TODO: convert and assign scalar

        // absorb scalar
        self.transcript_chip.absorb(&mut layouter, scalar)?;

        Ok(())
    }

    /// Squeezes a `LENGTH`-bit challenge from the transcript.
    /// We need a 160-bit challenge in practice
    pub fn squeeze_challenge<const LENGTH: usize>(
        &mut self,
        mut layouter: impl Layouter<C::Base>,
        prefix_challenge: AssignedCell<C::Base, C::Base>,
    ) -> Result<RangeConstrained<C::Base, AssignedCell<C::Base, C::Base>>, Error> {
        // absorb POSEIDON_PREFIX_CHALLENGE
        self.transcript_chip
            .absorb(&mut layouter, prefix_challenge.clone())?;
        self.transcript_chip
            .absorb(&mut layouter, prefix_challenge)?;

        let challenge = self.transcript_chip.squeeze(&mut layouter)?;
        self.transcript_chip.extract_bitrange(
            layouter.namespace(|| "extract bitrange"),
            &challenge,
            0..LENGTH,
        )
    }
}
