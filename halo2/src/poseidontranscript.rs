//! This module contains utilities and traits for dealing with Fiat-Shamir
//! transcripts.

use group::{ff::PrimeField, GroupEncoding};

use halo2_gadgets::poseidon::primitives::{
    Absorbing, ConstantLength, Domain, P128Pow5T3, Spec, Sponge as PoseidonSponge, Squeezing,
};
use halo2_proofs::arithmetic::{Coordinates, CurveAffine, FieldExt};

use std::io::{self, Read, Write};
use std::marker::PhantomData;

use lazy_static::lazy_static;
use pasta_curves::{pallas, vesta};

lazy_static! {
/// Prefix to a prover's message soliciting a challenge
pub static ref POSEIDON_PREFIX_CHALLENGE: vesta::Base = vesta::Base::from_u128(1);

/// Prefix to a prover's message containing a curve point
pub static ref POSEIDON_PREFIX_POINT: vesta::Base = vesta::Base::from_u128(2);

/// Prefix to a prover's message containing a scalar
pub static ref POSEIDON_PREFIX_SCALAR: vesta::Base = vesta::Base::from_u128(3);

}

use halo2_proofs::transcript::{EncodedChallenge, Transcript, TranscriptRead, TranscriptWrite};

const RATE: usize = 2;

/// A Poseidon transcript
#[derive(Debug)]
pub struct PoseidonRead<R: Read, E: EncodedChallenge<vesta::Affine>> {
    state: PoseidonSponge<vesta::Base, P128Pow5T3, Absorbing<vesta::Base, RATE>, 3, RATE>,
    reader: R,
    _marker: PhantomData<(vesta::Affine, E)>,
}

impl<R: Read, E: EncodedChallenge<vesta::Affine>> PoseidonRead<R, E> {
    /// Initialize a transcript given an input buffer.
    pub fn init(reader: R) -> Self {
        PoseidonRead {
            state: PoseidonSponge::new(
                <ConstantLength<2> as Domain<vesta::Base, 3>>::initial_capacity_element(),
            ),
            reader,
            _marker: PhantomData,
        }
    }
}

impl<R: Read> TranscriptRead<vesta::Affine, ChallengeBase<vesta::Affine>>
    for PoseidonRead<R, ChallengeBase<vesta::Affine>>
{
    fn read_point(&mut self) -> io::Result<vesta::Affine> {
        let mut compressed = <vesta::Scalar as PrimeField>::Repr::default();
        self.reader.read_exact(compressed.as_mut())?;
        let point: vesta::Affine = Option::from(vesta::Affine::from_bytes(&compressed))
            .ok_or_else(|| {
                io::Error::new(io::ErrorKind::Other, "invalid point encoding in proof")
            })?;
        self.common_point(point)?;

        Ok(point)
    }

    fn read_scalar(&mut self) -> io::Result<vesta::Scalar> {
        let mut data = <vesta::Scalar as PrimeField>::Repr::default();
        self.reader.read_exact(data.as_mut())?;
        let scalar: vesta::Scalar =
            Option::from(vesta::Scalar::from_repr(data)).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::Other,
                    "invalid field element encoding in proof",
                )
            })?;
        self.common_scalar(scalar)?;

        Ok(scalar)
    }
}

impl<R: Read> Transcript<vesta::Affine, ChallengeBase<vesta::Affine>>
    for PoseidonRead<R, ChallengeBase<vesta::Affine>>
{
    fn squeeze_challenge(&mut self) -> ChallengeBase<vesta::Affine> {
        self.state.absorb(*POSEIDON_PREFIX_CHALLENGE);
        self.state.absorb(*POSEIDON_PREFIX_CHALLENGE);
        // temporary workaround for moving Poseidon state out of the transcript
        let state = std::mem::replace(
            &mut self.state,
            PoseidonSponge::new(
                <ConstantLength<2> as Domain<vesta::Base, 3>>::initial_capacity_element(),
            ),
        );
        let mut state = state.finish_absorbing();
        let result = state.squeeze();
        self.state = state.finish_squeezing();

        ChallengeBase::<vesta::Affine>::new(&result)
    }

    fn common_point(&mut self, point: vesta::Affine) -> io::Result<()> {
        self.state.absorb(*POSEIDON_PREFIX_POINT);
        self.state.absorb(*POSEIDON_PREFIX_POINT);

        let coords: Coordinates<vesta::Affine> =
            Option::from(point.coordinates()).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::Other,
                    "cannot write points at infinity to the transcript",
                )
            })?;
        self.state.absorb(*coords.x());
        self.state.absorb(*coords.y());

        Ok(())
    }

    fn common_scalar(&mut self, scalar: vesta::Scalar) -> io::Result<()> {
        self.state.absorb(*POSEIDON_PREFIX_SCALAR);

        // Move scalar from scalar field into base field (which always fits
        // for Vesta).
        let base = vesta::Base::from_repr(scalar.to_repr()).unwrap();
        self.state.absorb(base);

        Ok(())
    }
}

/// A Poseidon transcript
#[derive(Debug)]
pub struct PoseidonWrite<W: Write, E: EncodedChallenge<vesta::Affine>> {
    state: PoseidonSponge<vesta::Base, P128Pow5T3, Absorbing<vesta::Base, RATE>, 3, RATE>,
    writer: W,
    _marker: PhantomData<(pallas::Affine, E)>,
}

impl<W: Write, E: EncodedChallenge<vesta::Affine>> PoseidonWrite<W, E> {
    /// Initialize a transcript given an output buffer.
    pub fn init(writer: W) -> Self {
        PoseidonWrite {
            state: PoseidonSponge::new(
                <ConstantLength<2> as Domain<vesta::Base, 3>>::initial_capacity_element(),
            ),
            writer,
            _marker: PhantomData,
        }
    }

    /// Conclude the interaction and return the output buffer (writer).
    pub fn finalize(self) -> W {
        // TODO: handle outstanding scalars? see issue #138
        self.writer
    }
}

impl<W: Write> TranscriptWrite<vesta::Affine, ChallengeBase<vesta::Affine>>
    for PoseidonWrite<W, ChallengeBase<vesta::Affine>>
{
    fn write_point(&mut self, point: vesta::Affine) -> io::Result<()> {
        self.common_point(point)?;
        let compressed = point.to_bytes();
        self.writer.write_all(compressed.as_ref())
    }
    fn write_scalar(&mut self, scalar: vesta::Scalar) -> io::Result<()> {
        self.common_scalar(scalar)?;
        let data = scalar.to_repr();
        self.writer.write_all(data.as_ref())
    }
}

impl<W: Write> Transcript<vesta::Affine, ChallengeBase<vesta::Affine>>
    for PoseidonWrite<W, ChallengeBase<vesta::Affine>>
{
    fn squeeze_challenge(&mut self) -> ChallengeBase<vesta::Affine> {
        self.state.absorb(*POSEIDON_PREFIX_CHALLENGE);
        self.state.absorb(*POSEIDON_PREFIX_CHALLENGE);

        // temporary workaround for moving Poseidon state out of the transcript
        let state = std::mem::replace(
            &mut self.state,
            PoseidonSponge::new(
                <ConstantLength<2> as Domain<vesta::Base, 3>>::initial_capacity_element(),
            ),
        );
        let mut state = state.finish_absorbing();
        let result = state.squeeze();
        self.state = state.finish_squeezing();
        ChallengeBase::<vesta::Affine>::new(&result)
    }

    fn common_point(&mut self, point: vesta::Affine) -> io::Result<()> {
        self.state.absorb(*POSEIDON_PREFIX_POINT);
        self.state.absorb(*POSEIDON_PREFIX_POINT);

        let coords: Coordinates<vesta::Affine> =
            Option::from(point.coordinates()).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::Other,
                    "cannot write points at infinity to the transcript",
                )
            })?;
        self.state.absorb(*coords.x());
        self.state.absorb(*coords.y());

        Ok(())
    }

    fn common_scalar(&mut self, scalar: vesta::Scalar) -> io::Result<()> {
        self.state.absorb(*POSEIDON_PREFIX_SCALAR);

        // Move scalar from scalar field into base field (which always fits
        // for Vesta).
        let base = vesta::Base::from_repr(scalar.to_repr()).unwrap();
        self.state.absorb(base);

        Ok(())
    }
}

#[test]
fn test_none_poseidon_transcript() {
    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ConstraintSystem, Error,
            SingleVerifier,
        },
        poly::commitment::Params,
    };
    use pasta_curves::EqAffine;
    use rand_core::OsRng;

    use group::ff::Field;

    #[derive(Clone, Copy)]
    struct MyCircuit;

    impl<F: Field> Circuit<F> for MyCircuit {
        type Config = ();

        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            *self
        }

        fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {}

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl halo2_proofs::circuit::Layouter<F>,
        ) -> Result<(), Error> {
            Ok(())
        }
    }

    let params: Params<EqAffine> = Params::new(3);
    let vk = keygen_vk(&params, &MyCircuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk.clone(), &MyCircuit).expect("keygen_pk should not fail");
    let mut transcript = PoseidonWrite::<_, ChallengeBase<_>>::init(vec![]);

    // Create proof with correct number of instances
    create_proof(&params, &pk, &[MyCircuit], &[&[]], OsRng, &mut transcript)
        .expect("proof generation should not fail");

    let proof = transcript.finalize();
    {
        let strategy = SingleVerifier::new(&params);
        let mut transcript = PoseidonRead::<_, ChallengeBase<_>>::init(&proof[..]);
        assert!(verify_proof(&params, &vk, strategy, &[&[]], &mut transcript,).is_ok());
    }
}

/// The field representation of a verifier challenge.
#[derive(Copy, Clone, Debug)]
pub struct ChallengeBase<C: CurveAffine> {
    inner: C::Base,
}

impl<C: CurveAffine> std::ops::Deref for ChallengeBase<C> {
    type Target = C::Base;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}
impl EncodedChallenge<pasta_curves::vesta::Affine> for ChallengeBase<pasta_curves::vesta::Affine> {
    type Input = pasta_curves::vesta::Base;

    fn new(challenge_input: &Self::Input) -> Self {
        ChallengeBase {
            inner: *challenge_input,
        }
    }
    fn get_scalar(&self) -> pasta_curves::vesta::Scalar {
        use group::ff::PrimeFieldBits;
        halo2_gadgets::endoscale::util::compute_endoscalar(
            &self.inner.to_le_bits().into_iter().collect::<Vec<bool>>(),
        )
    }
}
