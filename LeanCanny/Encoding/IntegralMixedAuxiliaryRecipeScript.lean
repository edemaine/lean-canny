/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeInstruction
public import LeanCanny.Geometry.CanonicalAuxiliaryRecipeLabels
/-! # The packed original record table is the exact seeded replay script -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem map_range_heq {A B : Type} {r : ℕ} (hAB : A=B) (f : ℕ → A) (g : Fin r → B)
    (h : ∀ i, HEq (f i.val) (g i)) : HEq ((List.range r).map f) (List.ofFn g) := by
  cases hAB
  apply heq_of_eq
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact eq_of_heq (h ⟨i,by simpa only [List.length_map,List.length_range] using hi⟩)

private theorem reverse_heq {A B : Type} (hAB : A=B) {xs : List A} {ys : List B} (h : HEq xs ys) :
    HEq xs.reverse ys.reverse := by
  cases hAB
  have H : xs=ys := eq_of_heq h
  cases H
  rfl

noncomputable def planAt {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :=
  IntegralMixedAuxiliaryEmptyPlan.plan (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
    (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q => ha (pairFst q))

theorem script_replay {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) :
    HEq ((planAt hn ht ha).rules (root original labels advice))
      (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.replay (n:=n original) (S:=n original+3)
        (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
        (ht:=(augmented n t original).degreeBound_le_dataSize) (recipeCap n t original)
        (seed n t original+1) labels) := by
  have HA : (parameters (dimension n) (term t)).ambient (root original labels advice)=n original+2 := by
    simp only [parameters,dimension,root_original]
  have HB : (parameters (dimension n) (term t)).width (root original labels advice)=scalarWidth n t original := by
    simp only [parameters,scalarWidth,scalarCeiling,spatialDegree,degreeCharge,augmented,dimension,term,root_original]
  have HTypes := congrArg₂ Instruction HA HB
  have HM := map_range_heq HTypes
    (fun j => nativeInstruction hn ht ha original labels advice j)
    (fun j : Fin (n original) => LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.recipeInstruction
      (n:=n original) (S:=n original+3) (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
      (ht:=(augmented n t original).degreeBound_le_dataSize) (recipeCap n t original)
      (seed n t original+1) j.val (labels j).1 (labels j).2)
    (fun j => nativeInstruction_recipe hn ht ha original labels advice j)
  have HCount : IntegralMixedEmptyUnitPlan.count (root original labels advice)=n original := by
    exact (IntegralMixedAuxiliaryPreparedRoot.pack_count original (words labels) advice).trans (words_length labels)
  change HEq (((List.range (IntegralMixedEmptyUnitPlan.count (root original labels advice))).map
    (fun j => nativeInstruction hn ht ha original labels advice j)).reverse) _
  rw [HCount]
  exact reverse_heq HTypes HM
end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
