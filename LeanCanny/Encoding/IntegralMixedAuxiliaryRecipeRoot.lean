/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryPreparedRoot
public import LeanCanny.Geometry.CanonicalAuxiliaryRecipeInstruction
/-! # Packed cut labels have the exact original source schedule -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def words {N : ℕ} (labels : Fin N → ℕ × ℕ) := List.ofFn (fun j =>
  IntegralMixedAuxiliaryLimitRecord.record N j.val 0 (labels j).1 (labels j).2)

noncomputable def root (original : List Bool) {N : ℕ} (labels : Fin N → ℕ × ℕ) (advice : List Bool) :=
  IntegralMixedAuxiliaryPreparedRoot.pack original (words labels) advice

theorem words_length {N : ℕ} (labels : Fin N → ℕ × ℕ) : (words labels).length=N := List.length_ofFn

theorem root_original (original : List Bool) {N : ℕ} (labels : Fin N → ℕ × ℕ) (advice : List Bool) :
    pairFst (root original labels advice)=original := pairFst_pair _ _

theorem root_code (original : List Bool) {N : ℕ} (labels : Fin N → ℕ × ℕ) (advice : List Bool) (j : Fin N) :
    IntegralMixedEmptyUnitPlan.code (root original labels advice) j.val=
      IntegralMixedAuxiliaryLimitRecord.record N j.val 0 (labels j).1 (labels j).2 := by
  unfold IntegralMixedEmptyUnitPlan.code IntegralMixedEmptyUnitPlan.records root
    IntegralMixedAuxiliaryPreparedRoot.pack IntegralMixedAuxiliaryPreparedRoot.packWords
  rw [pairSnd_pair,pairFst_pair,WordList.get_encode]
  simp only [words,List.getElem?_ofFn,dite_eq_left j.isLt,Option.getD_some]

theorem root_stateHorizon (n : List Bool → ℕ) (original : List Bool)
    (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) :
    stateHorizon (dimension n) (root original labels advice)=n original+3 :=
  IntegralMixedAuxiliaryPreparedRoot.pack_stateHorizon n original (words labels) advice (words_length labels)

theorem root_height (n : List Bool → ℕ) (t : List Bool → Term) (original : List Bool)
    (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) (birth : ℕ) :
    height (dimension n) (term t) (root original labels advice) birth=
      LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.nextHeight (n original) (n original+3)
        (scalarWidth (dimension n) (term t) (root original labels advice))
        (degreeCharge (dimension n) (term t) (root original labels advice)) 1^birth*
          (seed (dimension n) (term t) (root original labels advice)+1) := by
  unfold height
  rw [LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.recursiveHeight_eq_scheduled]
  unfold LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.scheduledHeight
  rw [root_stateHorizon]
  simp only [dimension,root_original]

theorem root_frozen (n : List Bool → ℕ) (original : List Bool)
    (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) (j : Fin (n original)) :
    frozen (dimension n) (root original labels advice) j.val=j.val := by
  unfold frozen
  simp only [dimension,root_original]
  exact min_eq_left j.isLt.le
end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
