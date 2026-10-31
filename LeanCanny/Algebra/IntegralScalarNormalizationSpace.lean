/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralNormalizationMatrixSpace
public import LeanCanny.Algebra.IntegralCriticalLeadingSpace

/-! # Native normalization with a scalar leading multiplication matrix

An integer selected coefficient acts as a scalar matrix modulo every
caller modulus. A normalization entry therefore reads one original
coefficient and one leading residue, then uses binary modular powering
and multiplication. The old matrix rank adds no matrix-power stage.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralScalarNormalizationBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family extends IntegralNormalizationMatrixBits.Family where
  leading : (c : List Bool) → ZMod (modulus c)
  leading_eq : ∀ c, coefficient c (degree c) = leading c • 1

structure Access (F : Family) extends IntegralNormalizationMatrixBits.Access F.toFamily where
  leading : List Bool → List Bool
  leading_eq : ∀ c, leading c = residueBits (F.leading c)

theorem scalar_entry (F : Family) (c : List Bool) :
    (F.coefficient c (F.index c) * F.coefficient c (F.degree c) ^ (F.degree c - 1 - F.index c)) (F.row c) (F.col c) =
      F.coefficient c (F.index c) (F.row c) (F.col c) * F.leading c ^ (F.degree c - 1 - F.index c) := by
  rw [F.leading_eq, smul_pow, one_pow, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply]
  exact mul_comm _ _

def coefficientQuery (F : Family) (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (F.index c))
    (pair (BinaryNatCode.encode (F.row c).val) (BinaryNatCode.encode (F.col c).val)))

theorem coefficientQuery_FP (F : Family) (a : Access F) : coefficientQuery F ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair a.index.bits_mem_FP (mem_FP_pair a.row.bits_mem_FP a.col.bits_mem_FP))

def powerPost (F : Family) (z : List Bool) : List Bool :=
  BinaryNat.powMod (pair (pairSnd z) (pair
    (BinaryNatCode.encode (F.degree (pairFst z) - 1 - F.index (pairFst z)))
    (BinaryNatCode.encode (F.modulus (pairFst z) - 1))))

theorem powerPost_FP (F : Family) (a : Access F) : powerPost F ∈ FP := by
  have HE : BinaryFn (fun z => F.degree (pairFst z) - 1 - F.index (pairFst z)) :=
    ((a.degree.sub (BinaryFn.const 1)).sub a.index).comp pairFst_mem_FP
  have HM : BinaryFn (fun z => F.modulus (pairFst z) - 1) := (a.modulus.sub (BinaryFn.const 1)).comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair pairSnd_mem_FP (mem_FP_pair HE.bits_mem_FP HM.bits_mem_FP)) BinaryNat.powMod_mem_FP

theorem powerPost_packet (F : Family) (c : List Bool) (x : ZMod (F.modulus c)) :
    powerPost F (pair c (residueBits x)) = residueBits (x ^ (F.degree c - 1 - F.index c)) := by
  simp only [powerPost, pairFst_pair, pairSnd_pair]
  exact IntegralScaledCharacteristicBits.pow_residue _ _ (F.modulus_ne_zero c) x

def multiplyPost (F : Family) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNatCode.encode (F.modulus (pairFst z))) (pairSnd z))

theorem multiplyPost_FP (F : Family) (a : Access F) : multiplyPost F ∈ FP := by
  have HM : BinaryFn (fun z => F.modulus (pairFst z)) := a.modulus.comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP pairSnd_mem_FP) BinaryNat.mulMod_mem_FP

theorem multiplyPost_packet (F : Family) (c : List Bool) (x y : ZMod (F.modulus c)) :
    multiplyPost F (pair c (pair (residueBits x) (residueBits y))) = residueBits (x * y) := by
  simp only [multiplyPost, pairFst_pair, pairSnd_pair]
  exact ArithmeticBits.mulMod_residueBits _ x y

attribute [local irreducible] powerPost multiplyPost IntegralNormalizationMatrixBits.Family.value ArithmeticBits.negate

theorem evaluator (F : Family) (a : Access F) (EC : SpaceFunction a.entry) (EL : SpaceFunction a.leading) :
    SpaceFunction F.toFamily.value := by
  have E := EC.precompose (coefficientQuery F) (coefficientQuery_FP F a)
  have EP := EL.withInput.postcompose (powerPost F) (powerPost_FP F a)
  refine ((E.pairOutputs EP).withInput.postcompose (multiplyPost F) (multiplyPost_FP F a)).congr
    (funext fun c => ?_)
  change multiplyPost F (pair c (pair (a.entry (coefficientQuery F c))
    (powerPost F (pair c (a.leading c))))) = F.toFamily.value c
  rw [a.leading_eq, powerPost_packet]
  unfold coefficientQuery
  rw [a.entry_eq, multiplyPost_packet]
  unfold IntegralNormalizationMatrixBits.Family.value
  rw [scalar_entry]

theorem negative_evaluator (F : Family) (a : Access F) (EC : SpaceFunction a.entry) (EL : SpaceFunction a.leading) :
    SpaceFunction F.toFamily.negativeValue := by
  have H := ((evaluator F a EC EL).withInput.postcompose (IntegralNormalizationMatrixBits.negateQuery F.toFamily)
    (IntegralNormalizationMatrixBits.negateQuery_FP F.toFamily a.toAccess)).postcompose
      ArithmeticBits.negate ArithmeticBits.negate_mem_FP
  refine H.congr (funext fun c => ?_)
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  simp only [Function.comp_apply, IntegralNormalizationMatrixBits.negateQuery, pairFst_pair, pairSnd_pair,
    IntegralNormalizationMatrixBits.Family.value, IntegralNormalizationMatrixBits.Family.negativeValue,
    ArithmeticBits.negate_residueBits]

end LeanCanny.Algebra.IntegralScalarNormalizationBits
