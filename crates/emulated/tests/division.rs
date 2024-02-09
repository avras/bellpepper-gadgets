use std::marker::PhantomData;

use bellpepper_emulated::field_element::{
    EmulatedFieldElement, EmulatedFieldParams, PseudoMersennePrime,
};
use ff::{Field, PrimeField, PrimeFieldBits};
use nova_snark::{
    provider,
    spartan::{direct::DirectSNARK, snark},
    traits::{circuit::StepCircuit, Engine},
};
use num_bigint::BigInt;

#[derive(Clone, Debug)]
pub struct BN256FpParams;

impl EmulatedFieldParams for BN256FpParams {
    fn num_limbs() -> usize {
        4
    }

    fn bits_per_limb() -> usize {
        64
    }

    fn modulus() -> BigInt {
        BigInt::parse_bytes(
            b"30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47",
            16,
        )
        .unwrap()
    }

    fn is_modulus_pseudo_mersenne() -> bool {
        false
    }

    fn pseudo_mersenne_params() -> Option<PseudoMersennePrime> {
        None
    }
}

pub type Fp<F> = EmulatedFieldElement<F, BN256FpParams>;

#[derive(Clone, Debug)]
struct DivisionCircuit<F: PrimeField + PrimeFieldBits, P: EmulatedFieldParams> {
    numerator: Fp<F>,
    denominator: Fp<F>,
    _params: PhantomData<P>,
}

impl<F, P> Default for DivisionCircuit<F, P>
where
    F: PrimeField + PrimeFieldBits,
    P: EmulatedFieldParams,
{
    fn default() -> Self {
        Self {
            numerator: Fp::<F>::zero(),
            denominator: Fp::<F>::zero(),
            _params: PhantomData,
        }
    }
}

impl<F, P> DivisionCircuit<F, P>
where
    F: PrimeField + PrimeFieldBits,
    P: EmulatedFieldParams,
{
    fn new(numer_val: BigInt, denom_val: BigInt) -> Self {
        Self {
            numerator: Fp::<F>::from(&numer_val),
            denominator: Fp::<F>::from(&denom_val),
            _params: PhantomData,
        }
    }
}

impl<F, P> StepCircuit<F> for DivisionCircuit<F, P>
where
    F: PrimeField + PrimeFieldBits,
    P: EmulatedFieldParams + Clone + Sync + Send,
{
    fn arity(&self) -> usize {
        1
    }

    fn synthesize<CS: bellpepper_core::ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[bellpepper_core::num::AllocatedNum<F>],
    ) -> Result<Vec<bellpepper_core::num::AllocatedNum<F>>, bellpepper_core::SynthesisError> {
        let numerator = self
            .numerator
            .allocate_field_element_unchecked(&mut cs.namespace(|| "alloc numerator"))?;
        let denominator = self
            .denominator
            .allocate_field_element_unchecked(&mut cs.namespace(|| "alloc denominator"))?;

        let ratio = numerator.divide(
            &mut cs.namespace(|| "calculate numerator divided by denominator"),
            &denominator,
        )?;

        let numerator_recalculated =
            ratio.mul(&mut cs.namespace(|| "ratio * denominator"), &denominator)?;

        EmulatedFieldElement::assert_is_equal(
            &mut cs.namespace(|| "numerator == recalculated numerator"),
            &numerator,
            &numerator_recalculated,
        )?;

        Ok(z.to_vec())
    }
}

#[test]
fn test_division() {
    type E = provider::PallasEngine;
    type EE = provider::ipa_pc::EvaluationEngine<E>;
    type S = snark::RelaxedR1CSSNARK<E, EE>;

    let circuit = DivisionCircuit::new(BigInt::from(4u64), BigInt::from(2u64));

    // produce keys
    let (pk, vk) =
        DirectSNARK::<E, S, DivisionCircuit<<E as Engine>::Scalar, BN256FpParams>>::setup(
            circuit.clone(),
        )
        .unwrap();

    // setup inputs
    let z0 = vec![<E as Engine>::Scalar::ONE];

    // produce a SNARK
    let res = DirectSNARK::prove(&pk, circuit.clone(), &z0);
    assert!(res.is_ok());

    let snark = res.unwrap();

    // verify the SNARK
    let io = vec![<E as Engine>::Scalar::ONE; 2];
    let res = snark.verify(&vk, &io);
    assert!(res.is_ok());
}
