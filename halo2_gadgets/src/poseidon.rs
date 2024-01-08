//! The Poseidon algebraic hash function.

use std::convert::TryInto;
use std::fmt;
use std::marker::PhantomData;

use group::ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{AssignedCell, Chip, Layouter},
    plonk::Error,
};

mod pow5;
pub use pow5::{Pow5Chip, Pow5Config, StateWord};

pub mod primitives;
use primitives::{Absorbing, ConstantLength, Domain, Spec, SpongeMode, Squeezing, State};

/// A word from the padded input to a Poseidon sponge.
#[derive(Clone, Debug)]
pub enum PaddedWord<F: Field> {
    /// A message word provided by the prover.
    Message(AssignedCell<F, F>),
    /// A padding word, that will be fixed in the circuit parameters.
    Padding(F),
}

/// The set of circuit instructions required to use the Poseidon permutation.
pub trait PoseidonInstructions<F: Field, S: Spec<F, T, RATE>, const T: usize, const RATE: usize>:
    Chip<F>
{
    /// Variable representing the word over which the Poseidon permutation operates.
    type Word: Clone + fmt::Debug + From<AssignedCell<F, F>> + Into<AssignedCell<F, F>>;

    /// Applies the Poseidon permutation to the given state.
    fn permute(
        &self,
        layouter: &mut impl Layouter<F>,
        initial_state: &State<Self::Word, T>,
    ) -> Result<State<Self::Word, T>, Error>;
}

/// The set of circuit instructions required to use the [`Sponge`] and [`Hash`] gadgets.
///
/// [`Hash`]: self::Hash
pub trait PoseidonSpongeInstructions<
    F: Field,
    S: Spec<F, T, RATE>,
    D: Domain<F, RATE>,
    const T: usize,
    const RATE: usize,
>: PoseidonInstructions<F, S, T, RATE>
{
    /// Returns the initial empty state for the given domain.
    fn initial_state(&self, layouter: &mut impl Layouter<F>)
        -> Result<State<Self::Word, T>, Error>;

    /// Adds the given input to the state.
    fn add_input(
        &self,
        layouter: &mut impl Layouter<F>,
        initial_state: &State<Self::Word, T>,
        input: &Absorbing<PaddedWord<F>, RATE>,
    ) -> Result<State<Self::Word, T>, Error>;

    /// Extracts sponge output from the given state.
    fn get_output(state: &State<Self::Word, T>) -> Squeezing<Self::Word, RATE>;
}

/// A word over which the Poseidon permutation operates.
#[derive(Debug)]
pub struct Word<
    F: Field,
    PoseidonChip: PoseidonInstructions<F, S, T, RATE>,
    S: Spec<F, T, RATE>,
    const T: usize,
    const RATE: usize,
> {
    inner: PoseidonChip::Word,
}

impl<
        F: Field,
        PoseidonChip: PoseidonInstructions<F, S, T, RATE>,
        S: Spec<F, T, RATE>,
        const T: usize,
        const RATE: usize,
    > Word<F, PoseidonChip, S, T, RATE>
{
    /// The word contained in this gadget.
    pub fn inner(&self) -> PoseidonChip::Word {
        self.inner.clone()
    }

    /// Construct a [`Word`] gadget from the inner word.
    pub fn from_inner(inner: PoseidonChip::Word) -> Self {
        Self { inner }
    }
}

fn poseidon_sponge<
    F: Field,
    PoseidonChip: PoseidonSpongeInstructions<F, S, D, T, RATE>,
    S: Spec<F, T, RATE>,
    D: Domain<F, RATE>,
    const T: usize,
    const RATE: usize,
>(
    chip: &PoseidonChip,
    mut layouter: impl Layouter<F>,
    state: &mut State<PoseidonChip::Word, T>,
    input: Option<&Absorbing<PaddedWord<F>, RATE>>,
) -> Result<Squeezing<PoseidonChip::Word, RATE>, Error> {
    if let Some(input) = input {
        *state = chip.add_input(&mut layouter, state, input)?;
    }
    *state = chip.permute(&mut layouter, state)?;
    Ok(PoseidonChip::get_output(state))
}

/// A Poseidon sponge.
#[derive(Debug)]
pub struct Sponge<
    F: Field,
    PoseidonChip: PoseidonSpongeInstructions<F, S, D, T, RATE>,
    S: Spec<F, T, RATE>,
    M: SpongeMode,
    D: Domain<F, RATE>,
    const T: usize,
    const RATE: usize,
> {
    chip: PoseidonChip,
    mode: M,
    state: State<PoseidonChip::Word, T>,
    _marker: PhantomData<D>,
}

impl<
        F: Field,
        PoseidonChip: PoseidonSpongeInstructions<F, S, D, T, RATE>,
        S: Spec<F, T, RATE>,
        D: Domain<F, RATE>,
        const T: usize,
        const RATE: usize,
    > Sponge<F, PoseidonChip, S, Absorbing<PaddedWord<F>, RATE>, D, T, RATE>
{
    /// Constructs a new duplex sponge for the given Poseidon specification.
    pub fn new(chip: PoseidonChip, mut layouter: impl Layouter<F>) -> Result<Self, Error> {
        chip.initial_state(&mut layouter).map(|state| Sponge {
            chip,
            mode: Absorbing(
                (0..RATE)
                    .map(|_| None)
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap(),
            ),
            state,
            _marker: PhantomData::default(),
        })
    }

    /// Absorbs an element into the sponge.
    pub fn absorb(
        &mut self,
        mut layouter: impl Layouter<F>,
        value: PaddedWord<F>,
    ) -> Result<(), Error> {
        for entry in self.mode.0.iter_mut() {
            if entry.is_none() {
                *entry = Some(value);
                return Ok(());
            }
        }

        // We've already absorbed as many elements as we can
        let _ = poseidon_sponge(
            &self.chip,
            layouter.namespace(|| "PoseidonSponge"),
            &mut self.state,
            Some(&self.mode),
        )?;
        self.mode = Absorbing::init_with(value);

        Ok(())
    }

    /// Transitions the sponge into its squeezing state.
    #[allow(clippy::type_complexity)]
    pub fn finish_absorbing(
        mut self,
        mut layouter: impl Layouter<F>,
    ) -> Result<Sponge<F, PoseidonChip, S, Squeezing<PoseidonChip::Word, RATE>, D, T, RATE>, Error>
    {
        let mode = poseidon_sponge(
            &self.chip,
            layouter.namespace(|| "PoseidonSponge"),
            &mut self.state,
            Some(&self.mode),
        )?;

        Ok(Sponge {
            chip: self.chip,
            mode,
            state: self.state,
            _marker: PhantomData::default(),
        })
    }
}

impl<
        F: Field,
        PoseidonChip: PoseidonSpongeInstructions<F, S, D, T, RATE>,
        S: Spec<F, T, RATE>,
        D: Domain<F, RATE>,
        const T: usize,
        const RATE: usize,
    > Sponge<F, PoseidonChip, S, Squeezing<PoseidonChip::Word, RATE>, D, T, RATE>
{
    /// Squeezes an element from the sponge.
    pub fn squeeze(&mut self, mut layouter: impl Layouter<F>) -> Result<AssignedCell<F, F>, Error> {
        loop {
            for entry in self.mode.0.iter_mut() {
                if let Some(inner) = entry.take() {
                    return Ok(inner.into());
                }
            }

            // We've already squeezed out all available elements
            self.mode = poseidon_sponge(
                &self.chip,
                layouter.namespace(|| "PoseidonSponge"),
                &mut self.state,
                None,
            )?;
        }
    }
    /// Transitions the sponge into its squeezing state.
    #[allow(clippy::type_complexity)]
    pub fn finish_squeezing(
        mut self,
        mut layouter: impl Layouter<F>,
    ) -> Result<Sponge<F, PoseidonChip, S, Absorbing<PaddedWord<F>, RATE>, D, T, RATE>, Error> {
        self.state = self.chip.permute(&mut layouter, &self.state)?;
        let mode = Absorbing(
            (0..RATE)
                .map(|_| None)
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        );

        Ok(Sponge {
            chip: self.chip,
            mode,
            state: self.state,
            _marker: PhantomData::default(),
        })
    }
}

/// A Poseidon hash function, built around a sponge.
#[derive(Debug)]
pub struct Hash<
    F: Field,
    PoseidonChip: PoseidonSpongeInstructions<F, S, D, T, RATE>,
    S: Spec<F, T, RATE>,
    D: Domain<F, RATE>,
    const T: usize,
    const RATE: usize,
> {
    sponge: Sponge<F, PoseidonChip, S, Absorbing<PaddedWord<F>, RATE>, D, T, RATE>,
}

impl<
        F: Field,
        PoseidonChip: PoseidonSpongeInstructions<F, S, D, T, RATE>,
        S: Spec<F, T, RATE>,
        D: Domain<F, RATE>,
        const T: usize,
        const RATE: usize,
    > Hash<F, PoseidonChip, S, D, T, RATE>
{
    /// Initializes a new hasher.
    pub fn init(chip: PoseidonChip, layouter: impl Layouter<F>) -> Result<Self, Error> {
        Sponge::new(chip, layouter).map(|sponge| Hash { sponge })
    }
}

impl<
        F: PrimeField,
        PoseidonChip: PoseidonSpongeInstructions<F, S, ConstantLength<L>, T, RATE>,
        S: Spec<F, T, RATE>,
        const T: usize,
        const RATE: usize,
        const L: usize,
    > Hash<F, PoseidonChip, S, ConstantLength<L>, T, RATE>
{
    /// Hashes the given input.
    pub fn hash(
        mut self,
        mut layouter: impl Layouter<F>,
        message: [AssignedCell<F, F>; L],
    ) -> Result<AssignedCell<F, F>, Error> {
        for (i, value) in message
            .into_iter()
            .map(PaddedWord::Message)
            .chain(<ConstantLength<L> as Domain<F, RATE>>::padding(L).map(PaddedWord::Padding))
            .enumerate()
        {
            self.sponge
                .absorb(layouter.namespace(|| format!("absorb_{}", i)), value)?;
        }
        self.sponge
            .finish_absorbing(layouter.namespace(|| "finish absorbing"))?
            .squeeze(layouter.namespace(|| "squeeze"))
    }
}

#[cfg(test)]
mod tests {
    use group::ff::Field;
    use halo2_proofs::{
        circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        pasta::Fp,
        plonk::{self, Circuit, ConstraintSystem, Error, SingleVerifier},
        poly::commitment::Params,
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };
    use pasta_curves::EqAffine;
    use rand::rngs::OsRng;

    use super::{primitives::Absorbing, Pow5Chip, Pow5Config};
    use crate::poseidon::primitives::{
        self as poseidon, ConstantLength, P128Pow5T3 as OrchardNullifier, Spec,
    };
    use std::convert::TryInto;
    use std::marker::PhantomData;

    struct DuplexCircuit<
        S: Spec<Fp, WIDTH, RATE>,
        const WIDTH: usize,
        const RATE: usize,
        const L: usize,
    > {
        message: Value<[Fp; L]>,
        // For the purpose of this test, witness the result.
        // TODO: Move this into an instance column.
        output: Value<Fp>,
        _spec: PhantomData<S>,
    }

    impl<S: Spec<Fp, WIDTH, RATE>, const WIDTH: usize, const RATE: usize, const L: usize>
        Circuit<Fp> for DuplexCircuit<S, WIDTH, RATE, L>
    {
        type Config = Pow5Config<Fp, WIDTH, RATE>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self {
                message: Value::unknown(),
                output: Value::unknown(),
                _spec: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Pow5Config<Fp, WIDTH, RATE> {
            let state = (0..WIDTH).map(|_| meta.advice_column()).collect::<Vec<_>>();
            let partial_sbox = meta.advice_column();

            let rc_a = (0..WIDTH).map(|_| meta.fixed_column()).collect::<Vec<_>>();
            let rc_b = (0..WIDTH).map(|_| meta.fixed_column()).collect::<Vec<_>>();

            meta.enable_constant(rc_b[0]);

            Pow5Chip::configure::<S>(
                meta,
                state.try_into().unwrap(),
                partial_sbox,
                rc_a.try_into().unwrap(),
                rc_b.try_into().unwrap(),
            )
        }

        fn synthesize(
            &self,
            config: Pow5Config<Fp, WIDTH, RATE>,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            let chip = Pow5Chip::construct(config.clone());

            let message: [AssignedCell<Fp, Fp>; L] = layouter.assign_region(
                || "load message",
                |mut region| {
                    let message_word = |i: usize| {
                        let value = self.message.map(|message_vals| message_vals[i]);
                        region.assign_advice(
                            || format!("load message_{}", i),
                            config.state[i],
                            0,
                            || value,
                        )
                    };

                    let message: Result<Vec<_>, Error> = (0..L).map(message_word).collect();
                    Ok(message?.try_into().unwrap())
                },
            )?;

            let mut sponge =
                super::Sponge::<_, _, S, Absorbing<_, RATE>, ConstantLength<L>, WIDTH, RATE>::new(
                    chip,
                    layouter.namespace(|| "init"),
                )?;

            let message = message
                .into_iter()
                .map(super::PaddedWord::Message)
                .collect::<Vec<_>>();

            let message_padding = super::PaddedWord::Padding(Fp::ZERO);
            for (i, message_word) in message.into_iter().enumerate() {
                sponge.absorb(
                    layouter.namespace(|| format!("sponge absorb {i}")),
                    message_word.clone(),
                )?;
                sponge.absorb(
                    layouter.namespace(|| format!("sponge padding {i}")),
                    message_padding.clone(),
                )?;
                sponge = sponge
                    .finish_absorbing(layouter.namespace(|| format!("sponge finish absorb {i}")))?
                    .finish_squeezing(
                        layouter.namespace(|| format!("sponge finish squeeze {i}")),
                    )?;
            }
            // absorb two more zeros so we can call finish_absorbing again
            sponge.absorb(
                layouter.namespace(|| format!("sponge final padding 1")),
                message_padding.clone(),
            )?;
            sponge.absorb(
                layouter.namespace(|| format!("sponge final padding 2")),
                message_padding.clone(),
            )?;

            let mut sponge =
                sponge.finish_absorbing(layouter.namespace(|| "sponge final finish absorbing"))?;
            let output = sponge.squeeze(layouter.namespace(|| "sponge"))?;

            layouter.assign_region(
                || "constrain output",
                |mut region| {
                    let expected_var = region.assign_advice(
                        || "load output",
                        config.state[0],
                        0,
                        || self.output,
                    )?;
                    region.constrain_equal(output.cell(), expected_var.cell())
                },
            )
        }
    }

    #[test]
    fn poseidon_duplex() {
        let rng = OsRng;
        use crate::poseidon::{primitives::Domain, Absorbing};

        let message = [Fp::random(rng), Fp::random(rng), Fp::random(rng)];

        const T: usize = 3;
        const RATE: usize = 2;
        let mut sponge =
            poseidon::Sponge::<_, OrchardNullifier, Absorbing<_, { RATE }>, { T }, { RATE }>::new(
                <ConstantLength<3> as Domain<_, { RATE }>>::initial_capacity_element(),
            );
        for value in message.into_iter() {
            sponge.absorb(value);
            sponge.absorb(Fp::ZERO);
            sponge = sponge.finish_absorbing().finish_squeezing();
        }
        // absorb two more zeros so we can call finish_absorbing again
        sponge.absorb(Fp::ZERO);
        sponge.absorb(Fp::ZERO);
        let output = sponge.finish_absorbing().squeeze();

        let k = 10;
        let circuit = DuplexCircuit::<OrchardNullifier, 3, 2, 3> {
            message: Value::known(message),
            output: Value::known(output),
            _spec: PhantomData,
        };
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));

        let params = Params::new(k);
        let vk = plonk::keygen_vk(&params, &circuit).unwrap();
        let pk = plonk::keygen_pk(&params, vk, &circuit).unwrap();

        let mut transcript = Blake2bWrite::<_, EqAffine, _>::init(vec![]);
        plonk::create_proof(
            &params,
            &pk,
            &[circuit],
            &[&[]],
            &mut OsRng,
            &mut transcript,
        )
        .unwrap();
        let proof = transcript.finalize();

        let strategy = SingleVerifier::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        assert!(
            plonk::verify_proof(&params, pk.get_vk(), strategy, &[&[]], &mut transcript).is_ok()
        );
    }
}
