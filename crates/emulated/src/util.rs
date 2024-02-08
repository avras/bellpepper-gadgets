use std::ops::Rem;

use bellpepper_core::boolean::AllocatedBit;
use bellpepper_core::num::{AllocatedNum, Num};
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError, Variable};
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

/// Range check a Num
pub fn range_check_num<Scalar, CS>(
    cs: &mut CS,
    num: &Num<Scalar>,
    num_bits: usize,
) -> Result<(), SynthesisError>
where
    Scalar: PrimeField + PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    range_check_lc(
        cs,
        &num.lc(Scalar::ONE),
        num.get_value().unwrap_or_default(),
        num_bits,
    )
}

/// Range check an expression represented by a LinearCombination
///
/// From `fits_in_bits` of `bellperson-nonnative`
pub fn range_check_lc<Scalar, CS>(
    cs: &mut CS,
    lc_input: &LinearCombination<Scalar>,
    lc_value: Scalar,
    num_bits: usize,
) -> Result<(), SynthesisError>
where
    Scalar: PrimeField + PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let value_bits = lc_value.to_le_bits();

    // Allocate all but the first bit.
    let bits: Vec<Variable> = (1..num_bits)
        .map(|i| {
            cs.alloc(
                || format!("bit {i}"),
                || {
                    let r = if value_bits[i] {
                        Scalar::ONE
                    } else {
                        Scalar::ZERO
                    };
                    Ok(r)
                },
            )
        })
        .collect::<Result<_, _>>()?;

    for (i, v) in bits.iter().enumerate() {
        cs.enforce(
            || format!("bit {i} is bit"),
            |lc| lc + *v,
            |lc| lc + CS::one() - *v,
            |lc| lc,
        )
    }

    // Last bit
    cs.enforce(
        || "last bit of variable is a bit".to_string(),
        |mut lc| {
            let mut f = Scalar::ONE;
            lc = lc + lc_input;
            for v in bits.iter() {
                f = f.double();
                lc = lc - (f, *v);
            }
            lc
        },
        |mut lc| {
            lc = lc + CS::one();
            let mut f = Scalar::ONE;
            lc = lc - lc_input;
            for v in bits.iter() {
                f = f.double();
                lc = lc + (f, *v);
            }
            lc
        },
        |lc| lc,
    );

    Ok(())
}

/// Range check a constant field element
pub fn range_check_constant<Scalar>(value: Scalar, num_bits: usize) -> Result<(), SynthesisError>
where
    Scalar: PrimeField + PrimeFieldBits,
{
    let value_bits = value.to_le_bits();
    let mut res = Scalar::ZERO;
    let mut coeff = Scalar::ONE;
    for i in 0..num_bits {
        if value_bits[i] {
            res += coeff;
        }
        coeff = coeff.double();
    }
    if res != value {
        eprintln!("value does not fit in the required number of bits");
        return Err(SynthesisError::Unsatisfiable);
    }

    Ok(())
}

/// Check that a Num equals a constant and return a bit
///
/// Based on `alloc_num_equals` in `Nova/src/gadgets/utils.rs`
pub fn alloc_num_equals_constant<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
    a: &Num<Scalar>,
    b: Scalar,
) -> Result<AllocatedBit, SynthesisError> {
    // Allocate and constrain `r`: result boolean bit.
    // It equals `true` if `a` equals `b`, `false` otherwise
    let a_value = a.get_value().unwrap_or_default();
    let r = AllocatedBit::alloc(cs.namespace(|| "r"), Some(a_value == b))?;

    // Allocate t s.t. t=1 if a == b else 1/(a - b)
    let t_value = if a_value == b {
        Scalar::ONE
    } else {
        (a_value - b).invert().unwrap()
    };
    let t = AllocatedNum::alloc(cs.namespace(|| "t"), || Ok(t_value))?;

    cs.enforce(
        || "t*(a - b) = 1 - r",
        |lc| lc + t.get_variable(),
        |lc| lc + &a.lc(Scalar::ONE) - &LinearCombination::from_coeff(CS::one(), b),
        |lc| lc + CS::one() - r.get_variable(),
    );

    cs.enforce(
        || "r*(a - b) = 0",
        |lc| lc + r.get_variable(),
        |lc| lc + &a.lc(Scalar::ONE) - &LinearCombination::from_coeff(CS::one(), b),
        |lc| lc,
    );

    Ok(r)
}

/// Convert a non-negative BigInt into a field element
pub fn bigint_to_scalar<Scalar>(value: &BigInt) -> Scalar
where
    Scalar: PrimeField + PrimeFieldBits,
{
    assert!(value.bits() as u32 <= Scalar::CAPACITY);
    assert!(!value.is_negative());

    let mut base = Scalar::from(u64::MAX);
    base += Scalar::ONE; // 2^64 in the field
    let mut coeff = Scalar::ONE;
    let mut res = Scalar::ZERO;

    let (_sign, digits) = value.to_u64_digits();
    for d in digits.into_iter() {
        let d_f = Scalar::from(d);
        res += d_f * coeff;
        coeff *= base;
    }
    res
}

/// Construct a [BigInt] from a vector of [BigInt] limbs with base equal to 2^num_bits_per_limb
pub fn recompose(limbs: &[BigInt], num_bits_per_limb: usize) -> Result<BigInt, SynthesisError> {
    if limbs.is_empty() {
        eprintln!("Empty input");
        return Err(SynthesisError::Unsatisfiable);
    }

    let mut res = BigInt::zero();
    for i in 0..limbs.len() {
        res <<= num_bits_per_limb;
        res += &limbs[limbs.len() - i - 1];
    }
    Ok(res)
}

/// Decompose a [BigInt] into a vector of [BigInt] limbs each occupying `num_bits_per_limb` bits.
pub fn decompose(
    input: &BigInt,
    num_bits_per_limb: usize,
    num_limbs: usize,
) -> Result<Vec<BigInt>, SynthesisError> {
    if input.bits() as usize > num_limbs * num_bits_per_limb {
        eprintln!("Not enough limbs to represent input {:?}", input);
        return Err(SynthesisError::Unsatisfiable);
    }

    let mut res = vec![BigInt::zero(); num_limbs];
    let base = BigInt::one() << num_bits_per_limb;
    let mut tmp = input.clone();
    for r in res.iter_mut() {
        *r = tmp.clone().rem(&base);
        tmp >>= num_bits_per_limb;
    }
    Ok(res)
}
