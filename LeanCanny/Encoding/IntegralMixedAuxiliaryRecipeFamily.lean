/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeState
public import LeanCanny.Algebra.IntegralMixedFramedFamilyRunView
/-! # The terminal saved family is the actual seeded recipe bank

The terminal family may use its padded source0. The comparison therefore
reframes both actual states explicitly, without identifying source0 with the
advanced terminal source.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def dataAt {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    IntegralMixedFramedHistoryFamilyBits.Data (parameters (dimension n) (term t)) (planAt hn ht ha) := by
  unfold planAt IntegralMixedAuxiliaryEmptyPlan.plan
  exact IntegralMixedAuxiliaryEmptyPlan.data (IntegralMixedAuxiliaryPreparedRoot.dimension_unary hn)
    (IntegralMixedAuxiliaryPreparedRoot.term_FP ht) (fun q => ha (pairFst q))

noncomputable def terminalKey {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice context : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt (root original labels advice)
    ((planAt hn ht ha).rules (root original labels advice)).length context

noncomputable def terminalState {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice context : List Bool) :
    State (IntegralMixedFramedHistoryFamilyBits.instruction (parameters (dimension n) (term t)) (planAt hn ht ha)
      (terminalKey hn ht ha original labels advice context)).source
      ((parameters (dimension n) (term t)).cap (pairFst (terminalKey hn ht ha original labels advice context))+1)
      ((parameters (dimension n) (term t)).width (pairFst (terminalKey hn ht ha original labels advice context)))
      (IntegralMixedFramedHistoryFamilyBits.commands (parameters (dimension n) (term t)) (planAt hn ht ha)
        (terminalKey hn ht ha original labels advice context)).length
      (Index (Fin 0) (IntegralMixedFramedHistoryFamilyBits.commands (parameters (dimension n) (term t)) (planAt hn ht ha)
        (terminalKey hn ht ha original labels advice context))) :=
  IntegralMixedFramedFamilyRunView.stateView (parameters (dimension n) (term t)) (planAt hn ht ha) (dataAt hn ht ha)
    (terminalKey hn ht ha original labels advice context)

section
attribute [local irreducible] dataAt terminalKey terminalState nativeRun IntegralMixedFramedFamilyRunView.stateView
  parameters scalarWidth scalarCeiling spatialDegree degreeCharge augmented root planAt

theorem terminalCap {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice context : List Bool)
    (R : SpatialSource (n original+2))
    (hR : PurePowerReductionBounds.dimension (n original+3) R.degree≤2^scalarWidth n t original) :
    PurePowerReductionBounds.dimension (n original+3) R.degree≤
      2^(parameters (dimension n) (term t)).width (pairFst (terminalKey hn ht ha original labels advice context)) := by
  unfold terminalKey
  rw [IntegralMixedFramedHistoryFamilyBits.keyAt_root]
  have HB : (parameters (dimension n) (term t)).width (root original labels advice)=scalarWidth n t original := by
    simp only [parameters,scalarWidth,scalarCeiling,spatialDegree,degreeCharge,augmented,dimension,term,root_original]
  rw [HB]
  exact hR

set_option backward.isDefEq.respectTransparency true in
theorem terminalState_nativeRun {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice context : List Bool)
    (R : SpatialSource (n original+2))
    (hRkey : PurePowerReductionBounds.dimension (n original+3) R.degree≤
      2^(parameters (dimension n) (term t)).width (pairFst (terminalKey hn ht ha original labels advice context)))
    (hRnative : PurePowerReductionBounds.dimension (n original+3) R.degree≤
      2^(parameters (dimension n) (term t)).width (root original labels advice)) :
    HEq (reframe (terminalState hn ht ha original labels advice context) R hRkey)
      (reframe (nativeRun hn ht ha original labels advice) R hRnative) := by
  have Hroom:=(planAt hn ht ha).room (root original labels advice)
  have Hcap : ((planAt hn ht ha).rules (root original labels advice)).length≤
      (parameters (dimension n) (term t)).cap (root original labels advice)+1 := by omega
  have Hrun : ((planAt hn ht ha).rules (root original labels advice)).length≤
      (parameters (dimension n) (term t)).cap (root original labels advice)+1+1 := by omega
  unfold terminalKey at hRkey
  unfold terminalState terminalKey nativeRun initialNative
  exact
    IntegralMixedFramedFamilyRunView.stateView_reframe_full
      (parameters (dimension n) (term t)) (planAt hn ht ha) (dataAt hn ht ha)
      (root original labels advice) context Hcap Hrun R hRkey hRnative

end

attribute [local irreducible] dataAt terminalKey terminalState nativeRun
  parameters scalarWidth scalarCeiling spatialDegree root planAt

theorem terminalState_replay {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice context : List Bool)
    (R : SpatialSource (n original+2))
    (hR : PurePowerReductionBounds.dimension (n original+3) R.degree≤2^scalarWidth n t original)
    (hcs : (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.replay (n:=n original) (S:=n original+3)
      (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
      (ht:=(augmented n t original).degreeBound_le_dataSize) (recipeCap n t original)
      (seed n t original+1) labels).length≤n original+3+1) :
    HEq (reframe (terminalState hn ht ha original labels advice context) R
      (terminalCap hn ht ha original labels advice context R hR))
      (reframe (run (initialGeometric n t original)
        (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.replay (n:=n original) (S:=n original+3)
          (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
          (ht:=(augmented n t original).degreeBound_le_dataSize) (recipeCap n t original)
          (seed n t original+1) labels) hcs) R hR) := by
  have HB : (parameters (dimension n) (term t)).width (root original labels advice)=scalarWidth n t original := by
    simp only [parameters,scalarWidth,scalarCeiling,spatialDegree,degreeCharge,augmented,dimension,term,root_original]
  have hRN : PurePowerReductionBounds.dimension (n original+3) R.degree≤
      2^(parameters (dimension n) (term t)).width (root original labels advice) := by rw [HB]; exact hR
  exact (terminalState_nativeRun hn ht ha original labels advice context R
    (terminalCap hn ht ha original labels advice context R hR) hRN).trans
      (nativeRun_replay hn ht ha original labels advice R hR hRN hcs)
end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
