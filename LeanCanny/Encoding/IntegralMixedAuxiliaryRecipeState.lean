/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeScript
public import LeanCanny.Algebra.IntegralMixedFramedRunTransport
/-! # Actual packed empty runs and seeded geometric replays have the same bank -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def initialNative {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.initial (parameters (dimension n) (term t))
    (planAt hn ht ha) (root original labels advice)

noncomputable def initialGeometric (n : List Bool → ℕ) (t : List Bool → Term) (original : List Bool) :=
  LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.seededInitialState (n:=n original) (S:=n original+3)
    (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t original)
    (augmented n t original).degreeBound_le_dataSize (recipeCap n t original) (seed n t original+1)

theorem initial_source_heq {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) :
    HEq ((planAt hn ht ha).initialSource (root original labels advice))
      (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.source 0 (degreeCharge n t original) (t original)
        (augmented n t original).degreeBound_le_dataSize 0 (scalarWidth n t original) (seed n t original+1)) := by
  simpa only [LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.recipeSource,pow_zero,one_mul,
    currentSource,planAt,IntegralMixedAuxiliaryEmptyPlan.plan,IntegralMixedEmptyUnitPlan.plan] using
    currentSource_recipe_le hn ht ha original labels advice 0 (Nat.zero_le _)

theorem initial_heq {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) :
    HEq (initialNative hn ht ha original labels advice) (initialGeometric n t original) := by
  have HA : (parameters (dimension n) (term t)).ambient (root original labels advice)=n original+2 := by
    simp only [parameters,dimension,root_original]
  have HB : (parameters (dimension n) (term t)).width (root original labels advice)=scalarWidth n t original := by
    simp only [parameters,scalarWidth,scalarCeiling,spatialDegree,degreeCharge,augmented,dimension,term,root_original]
  have HS : (parameters (dimension n) (term t)).cap (root original labels advice)+1=n original+3 :=
    root_stateHorizon n original labels advice
  exact IntegralMixedFramedRunTransport.base_zero_heq HA HS HB
    (initial_source_heq hn ht ha original labels advice)
    (initialNative hn ht ha original labels advice).critical_cap (initialGeometric n t original).critical_cap

noncomputable def nativeRun {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) :=
  run (initialNative hn ht ha original labels advice) ((planAt hn ht ha).rules (root original labels advice))
    (by have H:=(planAt hn ht ha).room (root original labels advice); omega)

theorem nativeRun_replay {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool)
    (R : SpatialSource (n original+2))
    (hR : PurePowerReductionBounds.dimension (n original+3) R.degree≤2^scalarWidth n t original)
    (hRnative : PurePowerReductionBounds.dimension (n original+3) R.degree≤
      2^(parameters (dimension n) (term t)).width (root original labels advice))
    (hcs : (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.replay (n:=n original) (S:=n original+3)
      (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
      (ht:=(augmented n t original).degreeBound_le_dataSize) (recipeCap n t original)
      (seed n t original+1) labels).length≤n original+3+1) :
    HEq (reframe (nativeRun hn ht ha original labels advice) R hRnative)
      (reframe (run (initialGeometric n t original)
        (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.replay (n:=n original) (S:=n original+3)
          (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
          (ht:=(augmented n t original).degreeBound_le_dataSize) (recipeCap n t original)
          (seed n t original+1) labels) hcs) R hR) := by
  have HA : (parameters (dimension n) (term t)).ambient (root original labels advice)=n original+2 := by
    simp only [parameters,dimension,root_original]
  have HB : (parameters (dimension n) (term t)).width (root original labels advice)=scalarWidth n t original := by
    simp only [parameters,scalarWidth,scalarCeiling,spatialDegree,degreeCharge,augmented,dimension,term,root_original]
  have HS : (parameters (dimension n) (term t)).cap (root original labels advice)+1=n original+3 :=
    root_stateHorizon n original labels advice
  have hNative : ((planAt hn ht ha).rules (root original labels advice)).length≤
      (parameters (dimension n) (term t)).cap (root original labels advice)+1+1 := by
    have H:=(planAt hn ht ha).room (root original labels advice)
    omega
  exact IntegralMixedFramedRunTransport.reframe_run_zero_heq HA HS HB
    (initial_source_heq hn ht ha original labels advice)
    (initialNative hn ht ha original labels advice) (initialGeometric n t original)
    (initial_heq hn ht ha original labels advice)
    ((planAt hn ht ha).rules (root original labels advice))
    (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.replay (n:=n original) (S:=n original+3)
      (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
      (ht:=(augmented n t original).degreeBound_le_dataSize) (recipeCap n t original) (seed n t original+1) labels)
    (script_replay hn ht ha original labels advice) hNative hcs R hRnative hR
end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
