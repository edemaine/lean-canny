/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationInverseQuery
public import LeanCanny.Computation.DependentTwoCallController
/-! # An adaptive inverse-coefficient request with native local processing -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ArithmeticBits.negate

abbrev IndexMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .clearedGridSum q → matrixDimension P F q < modulus P q → answer q = indexValue P F q

theorem indexTask_reply (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : IndexMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5) :
    answer (indexTask P F q) = BinaryNatCode.encode
      (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natTrailingDegree := by
  have HS : IntegralMixedVirtualTaskBits.saved P (indexTask P F q) = IntegralMixedVirtualTaskBits.saved P q :=
    IntegralMixedNormalizationFieldBits.query_saved P id .clearedGridSum _ _ q
  have HD : matrixDimension P F (indexTask P F q) = matrixDimension P F q := congrArg (dimension F) HS
  have HV : IntegralMixedVirtualCaps.valid P (indexTask P F q) := by
    unfold IntegralMixedVirtualCaps.valid indexTask
    rw [IntegralMixedNormalizationFieldBits.query_birth, IntegralMixedNormalizationFieldBits.query_root]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P (indexTask P F q) = 5 := by
    unfold indexTask
    rw [IntegralMixedNormalizationFieldBits.query_routine]
    exact hr
  have HP : isPhase .clearedGridSum (indexTask P F q) :=
    IntegralMixedNormalizationFieldBits.query_phase P id .clearedGridSum _ _ q
  have HM : matrixDimension P F (indexTask P F q) < modulus P (indexTask P F q) := by
    rw [HD, indexTask_modulus P F g q hv]
    exact Nat.lt_succ_self _
  exact (hx _ HV HR HP HM).trans (indexTask_value P F g q hv)

def inversePost (P : Parameters) (z : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (BinaryNatCode.encode (modulus P (pairFst z))) (pairSnd (pairSnd z)))

theorem inversePost_FP (P : Parameters) (a : Access P) : inversePost P ∈ FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  exact mem_FP_comp
    (f := fun z => pair (BinaryNatCode.encode (modulus P (pairFst z))) (pairSnd (pairSnd z)))
    (g := ArithmeticBits.negate)
    (mem_FP_pair HM.bits_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)) ArithmeticBits.negate_mem_FP

noncomputable def inverseValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits ((IntegralParameterInverse.inverse (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly).coeff
    (get P .target q) : ZMod (modulus P q))

theorem inverse_result (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hi : IndexMatches P F answer) (hc : CharacteristicMatches P F answer)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 5) (hk : get P .target q ≤ matrixDimension P F q) :
    DependentTwoCall.result (indexTask P F) (inverseTask P) (inversePost P) answer q = inverseValue P F q := by
  unfold DependentTwoCall.result
  rw [indexTask_reply P F g answer hi q hv hr, inverseTask_reply P F g answer hc q hv hr hk]
  simp only [inversePost, pairFst_pair, pairSnd_pair]
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  rw [ArithmeticBits.negate_residueBits]
  simp only [inverseValue, IntegralParameterInverse.coeff_inverse, Int.cast_neg]

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
