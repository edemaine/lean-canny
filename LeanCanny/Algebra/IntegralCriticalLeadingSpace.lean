/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralFrozenPowerConstantSpace
public import LeanCanny.Algebra.IntegralScaledCharacteristicSpace
public import LeanCanny.Algebra.ModularNatMulFP

/-! # Native common integer leading coefficients of cleared critical rows

The actual common leading coefficient is a*q^D*D. Binary modular powering
uses the supplied denominator residue and binary allowance. Neither a
signed power nor an inverse modulo the caller's modulus is serialized.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalLeadingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralFrozenPowerBits
set_option backward.isDefEq.respectTransparency false

noncomputable def value (S : Source) (c : List Bool) : List Bool :=
  residueBits (((S.leading c * S.denominator c ^ S.allowance c) * (S.allowance c : ℤ) : ℤ) : ZMod (S.modulus c))

def powerPost (S : Source) (z : List Bool) : List Bool :=
  BinaryNat.powMod (pair (pairSnd z) (pair (BinaryNatCode.encode (S.allowance (pairFst z)))
    (BinaryNatCode.encode (S.modulus (pairFst z) - 1))))

theorem powerPost_FP (S : Source) (a : Access S) : powerPost S ∈ FP := by
  have HE : BinaryFn (fun z => S.allowance (pairFst z)) := a.allowance.comp pairFst_mem_FP
  have HM : BinaryFn (fun z => S.modulus (pairFst z) - 1) := (a.modulus.sub (BinaryFn.const 1)).comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair pairSnd_mem_FP (mem_FP_pair HE.bits_mem_FP HM.bits_mem_FP)) BinaryNat.powMod_mem_FP

theorem powerPost_packet (S : Source) (c : List Bool) (x : ZMod (S.modulus c)) :
    powerPost S (pair c (residueBits x)) = residueBits (x ^ S.allowance c) := by
  simp only [powerPost, pairFst_pair, pairSnd_pair]
  exact IntegralScaledCharacteristicBits.pow_residue _ _ (S.modulus_ne_zero c) x

def degreePost (S : Source) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNatCode.encode (S.modulus (pairFst z)))
    (pair (pairSnd z) (BinaryNatCode.encode (S.allowance (pairFst z)))))

theorem degreePost_FP (S : Source) (a : Access S) : degreePost S ∈ FP := by
  have HM : BinaryFn (fun z => S.modulus (pairFst z)) := a.modulus.comp pairFst_mem_FP
  have HE : BinaryFn (fun z => S.allowance (pairFst z)) := a.allowance.comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP (mem_FP_pair pairSnd_mem_FP HE.bits_mem_FP)) BinaryNat.mulMod_mem_FP

theorem degreePost_packet (S : Source) (c : List Bool) (x : ZMod (S.modulus c)) :
    degreePost S (pair c (residueBits x)) = residueBits (x * (S.allowance c : ZMod (S.modulus c))) := by
  simp only [degreePost, pairFst_pair, pairSnd_pair]
  exact ArithmeticBits.mulMod_nat_residueBits _ x _

attribute [local irreducible] value powerPost degreePost IntegralFrozenPowerBits.multiplyPost

theorem evaluator (S : Source) (a : Access S) (EQ : SpaceFunction a.denominator) (EA : SpaceFunction a.leading) :
    SpaceFunction (value S) := by
  have EP := EQ.withInput.postcompose (powerPost S) (powerPost_FP S a)
  have EM := (EA.pairOutputs EP).withInput.postcompose (IntegralFrozenPowerBits.multiplyPost S)
    (IntegralFrozenPowerBits.multiplyPost_FP S a)
  refine (EM.withInput.postcompose (degreePost S) (degreePost_FP S a)).congr (funext fun c => ?_)
  change degreePost S (pair c (IntegralFrozenPowerBits.multiplyPost S
    (pair c (pair (a.leading c) (powerPost S (pair c (a.denominator c))))))) = _
  rw [a.denominator_eq, a.leading_eq, powerPost_packet, IntegralFrozenPowerBits.multiplyPost_packet,
    degreePost_packet]
  unfold value
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]

end LeanCanny.Algebra.IntegralCriticalLeadingBits
