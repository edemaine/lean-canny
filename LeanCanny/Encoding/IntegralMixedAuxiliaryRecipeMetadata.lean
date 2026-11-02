/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeFamily
/-! # Exact terminal birth, width, horizon and carrier of packed recipe roots -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
set_option backward.isDefEq.respectTransparency false

private theorem list_length_heq {A B : Type} (hAB : A=B) (xs : List A) (ys : List B) (h : HEq xs ys) :
    xs.length=ys.length := by
  cases hAB
  cases eq_of_heq h
  rfl

theorem script_length {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) :
    ((planAt hn ht ha).rules (root original labels advice)).length=n original := by
  have HA : (parameters (dimension n) (term t)).ambient (root original labels advice)=n original+2 := by
    simp only [parameters,dimension,root_original]
  have HB : (parameters (dimension n) (term t)).width (root original labels advice)=scalarWidth n t original := by
    simp only [parameters,scalarWidth,scalarCeiling,spatialDegree,degreeCharge,augmented,dimension,term,root_original]
  exact (list_length_heq (congrArg₂ Instruction HA HB) _ _
    (script_replay hn ht ha original labels advice)).trans
      (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.replay_length _ _ labels)

theorem terminal_root {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice context : List Bool) :
    pairFst (terminalKey hn ht ha original labels advice context)=root original labels advice := by
  unfold terminalKey
  exact IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _

theorem terminal_horizon {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice context : List Bool) :
    (parameters (dimension n) (term t)).cap (pairFst (terminalKey hn ht ha original labels advice context))+1=n original+3 := by
  rw [terminal_root]
  exact root_stateHorizon n original labels advice

theorem terminal_width {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice context : List Bool) :
    (parameters (dimension n) (term t)).width (pairFst (terminalKey hn ht ha original labels advice context))=scalarWidth n t original := by
  rw [terminal_root]
  simp only [parameters,scalarWidth,scalarCeiling,spatialDegree,degreeCharge,augmented,dimension,term,root_original]

attribute [local irreducible] parameters planAt root terminalKey

theorem terminal_birth {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice context : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.commands (parameters (dimension n) (term t)) (planAt hn ht ha)
      (terminalKey hn ht ha original labels advice context)).length=n original := by
  have Hroom:=(planAt hn ht ha).room (root original labels advice)
  have HC : ((planAt hn ht ha).rules (root original labels advice)).length≤
      (parameters (dimension n) (term t)).cap (root original labels advice)+1 := by omega
  unfold terminalKey IntegralMixedFramedHistoryFamilyBits.commands
  rw [paddedPast_length,IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ _ _ _ HC]
  exact script_length hn ht ha original labels advice

theorem terminal_index {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice context : List Bool) :
    Index (Fin 0) (IntegralMixedFramedHistoryFamilyBits.commands (parameters (dimension n) (term t)) (planAt hn ht ha)
      (terminalKey hn ht ha original labels advice context))=
    Index (Fin 0) (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.replay (n:=n original) (S:=n original+3)
      (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
      (ht:=(augmented n t original).degreeBound_le_dataSize) (recipeCap n t original)
      (seed n t original+1) labels) := by
  have HA : (parameters (dimension n) (term t)).ambient (root original labels advice)=n original+2 := by
    simp only [parameters,dimension,root_original]
  have HB : (parameters (dimension n) (term t)).width (root original labels advice)=scalarWidth n t original := by
    simp only [parameters,scalarWidth,scalarCeiling,spatialDegree,degreeCharge,augmented,dimension,term,root_original]
  have Hroom:=(planAt hn ht ha).room (root original labels advice)
  have HC : ((planAt hn ht ha).rules (root original labels advice)).length≤
      (parameters (dimension n) (term t)).cap (root original labels advice)+1 := by omega
  unfold terminalKey
  exact (IntegralMixedFramedFamilyRunView.commands_index_full (parameters (dimension n) (term t))
    (planAt hn ht ha) (root original labels advice) context HC).trans
      (IntegralMixedFramedRunTransport.index_zero_eq HA HB _ _ (script_replay hn ht ha original labels advice))
end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
