/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeightReferenceSum
/-! # The modular affine constant and reference sum use original cells only -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeightAffineSumBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedScalarCellsBits (cell Primitive)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus ArithmeticBits.combine

noncomputable def coefficient (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (tag : ℕ) (z : List Bool) :=
  IntegralMixedFramedHeightCellAccessBits.read P D J tag (pair z (BinaryNatCode.encode 0))

theorem coefficient_space (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : Primitive P D J) (tag : ℕ) :
    SpaceFunction (coefficient P D J tag) :=
  (IntegralMixedFramedHeightCellAccessBits.read_space P D J hp tag).precompose (fun z => pair z (BinaryNatCode.encode 0))
    (mem_FP_pair id_mem_FP (constFn_mem_FP _))

theorem coefficient_value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (tag : ℕ) (z : List Bool) :
    coefficient P D J tag z = residueBits (cell P D J (pairFst z) tag 0 : ZMod (modulus P (pairFst z))) :=
  IntegralMixedFramedHeightCellAccessBits.read_packet P D J tag z 0

def diagonal (P : Parameters) (z : List Bool) : Prop :=
  IntegralMixedHeightTableQueryBits.oldRow P (pairFst z) = IntegralMixedHeightTableQueryBits.oldCol P (pairFst z)

theorem diagonal_FP (P : Parameters) (a : Access P) : FPPred (diagonal P) := by
  have HR : BinaryFn (fun z => IntegralMixedHeightTableQueryBits.oldRow P (pairFst z)) :=
    (IntegralMixedHeightTableQueryBits.oldRow_binary P a).comp pairFst_mem_FP
  have HT : BinaryFn (fun z => IntegralMixedHeightTableQueryBits.oldCol P (pairFst z)) :=
    (IntegralMixedHeightTableQueryBits.oldCol_binary P a).comp pairFst_mem_FP
  exact HR.eq HT

noncomputable def diagonalConstant (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :=
  if diagonal P z then coefficient P D J 0 z else []

theorem diagonalConstant_space (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : Primitive P D J) :
    SpaceFunction (diagonalConstant P D J) := by
  have E := SpaceFunction.branch _ (diagonal_FP P a).flag_mem_FP (coefficient_space P D J hp 0) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun z => by simp only [decide_eq_true_eq]; rfl)

noncomputable def diagonalScalar (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) : ZMod (modulus P (pairFst z)) :=
  if diagonal P z then cell P D J (pairFst z) 0 0 else 0

theorem diagonalConstant_value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :
    diagonalConstant P D J z = residueBits (diagonalScalar P D J z) := by
  by_cases HD : diagonal P z
  · rw [diagonalConstant, ite_eq_left HD, coefficient_value, diagonalScalar, ite_eq_left HD]
  · rw [diagonalConstant, ite_eq_right HD, diagonalScalar, ite_eq_right HD]
    exact ArithmeticBits.zero_residueBits _

def finish (P : Parameters) (p : List Bool) :=
  ArithmeticBits.combine (pair (BinaryNatCode.encode (modulus P (pairFst (pairFst p)))) (pairSnd p))

theorem finish_FP (P : Parameters) (a : Access P) : finish P ∈ FP := by
  have HM : BinaryFn (fun p => modulus P (pairFst (pairFst p))) := (modulus_binary P a).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP pairSnd_mem_FP) ArithmeticBits.combine_mem_FP

noncomputable def value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :=
  finish P (pair z (pair (IntegralMixedFramedHeightReferenceSumBits.value P D J z)
    (pair (IntegralMixedFramedHeightBankProductBits.value P z) (diagonalConstant P D J z))))

theorem value_space (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : Primitive P D J) :
    SpaceFunction (value P D J) :=
  ((SpaceFunction.ofFP _ id_mem_FP).pairOutputs ((IntegralMixedFramedHeightReferenceSumBits.value_space P a D J hp).pairOutputs
    ((SpaceFunction.ofFP _ (IntegralMixedFramedHeightBankProductBits.value_FP P a)).pairOutputs (diagonalConstant_space P a D J hp)))).postcompose (finish P) (finish_FP P a)

noncomputable def scalar (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) : ZMod (modulus P (pairFst z)) :=
  (∑ i ∈ Finset.range (birth P (pairFst z)), IntegralMixedFramedHeightReferenceSumBits.scalar P D J z i) +
    (∏ i ∈ Finset.range (birth P (pairFst z)), IntegralMixedFramedHeightBankProductBits.scalar P z i) * diagonalScalar P D J z

theorem value_eq (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :
    value P D J z = residueBits (scalar P D J z) := by
  rw [value, IntegralMixedFramedHeightReferenceSumBits.value, IntegralMixedFramedHeightBankProductBits.value, diagonalConstant_value]
  simp only [finish, pairFst_pair, pairSnd_pair]
  let : NeZero (modulus P (pairFst z)) := ⟨modulus_ne_zero P (pairFst z)⟩
  exact ArithmeticBits.combine_residueBits _ _ _ _

end LeanCanny.Algebra.IntegralMixedFramedHeightAffineSumBits
