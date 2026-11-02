/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeSource
/-! # Actual packed instructions are the literal geometric recipe instructions -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private noncomputable def unitInstruction {A B : ℕ} (P : SpatialSource A) (hA : 0<A)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (A+1) P.degree≤2^B) (b : ℕ) (code : List Bool) : Instruction A B where
  source := P
  source_cap := (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
    PurePowerReductionBounds.dimension (A+1) P.degree≤IntegralMixedExceptionalBounds.auxiliaryCap (A+1) P.degree).trans hcap
  command := IntegralMixedCanonicalUnitRuleBits.command P hA b code hcap

private theorem unitInstruction_heq {A A' B B' : ℕ} {P : SpatialSource A} {Q : SpatialSource A'}
    (hA : A=A') (hB : B=B') (hP : HEq P Q) (ha : 0<A) (ha' : 0<A')
    (hc : IntegralMixedExceptionalBounds.auxiliaryCap (A+1) P.degree≤2^B)
    (hc' : IntegralMixedExceptionalBounds.auxiliaryCap (A'+1) Q.degree≤2^B') (b : ℕ) (code : List Bool) :
    HEq (unitInstruction P ha hc b code) (unitInstruction Q ha' hc' b code) := by
  cases hA
  cases hB
  have H : P=Q := eq_of_heq hP
  cases H
  rfl

private theorem unitInstruction_record {N B : ℕ} (P : SpatialSource (N+2))
    (hc : IntegralMixedExceptionalBounds.auxiliaryCap (N+3) P.degree≤2^B) (b c d : ℕ) :
    unitInstruction P (by omega) hc b (IntegralMixedAuxiliaryLimitRecord.record N b 0 c d) =
      IntegralMixedAuxiliaryLimitRecord.instruction P b 0 c d hc := by
  unfold unitInstruction IntegralMixedAuxiliaryLimitRecord.instruction
  simp only [Nat.zero_add]

noncomputable def nativeInstruction {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) (birth : ℕ) :=
  IntegralMixedEmptyUnitPlan.step (parameters (dimension n) (term t))
    (IntegralMixedAuxiliaryEmptyPlan.originals (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
      (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q => ha (pairFst q)))
    (ambient_positive (dimension n) (term t)) (auxiliary_cap (dimension n) (term t))
    (root original labels advice) birth

theorem nativeInstruction_recipe {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) (j : Fin (n original)) :
    HEq (nativeInstruction hn ht ha original labels advice j.val)
      (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.recipeInstruction (n:=n original) (S:=n original+3)
        (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
        (ht:=(augmented n t original).degreeBound_le_dataSize) (recipeCap n t original)
        (seed n t original+1) j.val (labels j).1 (labels j).2) := by
  have HA : (parameters (dimension n) (term t)).ambient (root original labels advice)=n original+2 := by
    simp only [parameters,dimension,root_original]
  have HB : (parameters (dimension n) (term t)).width (root original labels advice)=scalarWidth n t original := by
    simp only [parameters,scalarWidth,scalarCeiling,spatialDegree,degreeCharge,augmented,dimension,term,root_original]
  have HL : nativeInstruction hn ht ha original labels advice j.val=
      unitInstruction (currentSource hn ht ha original labels advice j.val)
        (ambient_positive (dimension n) (term t) (root original labels advice))
        (auxiliary_cap (dimension n) (term t) (root original labels advice)) j.val
        (IntegralMixedEmptyUnitPlan.code (root original labels advice) j.val) := rfl
  rw [root_code] at HL
  refine (heq_of_eq HL).trans ?_
  have H := unitInstruction_heq HA HB (currentSource_recipe hn ht ha original labels advice j)
    (ambient_positive (dimension n) (term t) (root original labels advice)) (by omega)
    (auxiliary_cap (dimension n) (term t) (root original labels advice))
    (recipeCap n t original) j.val (IntegralMixedAuxiliaryLimitRecord.record (n original) j.val 0 (labels j).1 (labels j).2)
  refine H.trans (heq_of_eq ?_)
  exact unitInstruction_record _ _ _ _ _
end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
