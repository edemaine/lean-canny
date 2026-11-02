/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliarySavedFields
public import LeanCanny.Encoding.IntegralMixedEmptyUnitData
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalTiltedNativeBody
/-! # A concrete original-only description and empty auxiliary plan -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def description {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP)
    (ha : ∀ root,(t root).arity≤n root) : FlatAffineExceptionalCanonicalTiltedNative.Description (parameters n t) where
  term := augmented n t
  frozen := frozen n
  tilt root _ := n root
  exponent := levelExponent n t
  degree _ := rfl
  term_FP := LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.auxiliaryTerm_FP hn ht
  frozen_native := frozen_packet_unary hn
  tilt_native := hn.comp pairFst_mem_FP
  exponent_native := levelExponent_packet_binary hn ht
  term_scope := source_scope n t ha
  tilt_scope root _ := (tilt_scope n t root).le
  factor := factor n t
  seed := seed n t
  factor_native := factor_binary hn ht
  seed_native := seed_binary hn ht
  factor_positive root := by unfold factor; omega

noncomputable abbrev originals {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :=
  FlatAffineExceptionalCanonicalTiltedNative.originals (parameters n t) (description hn ht ha)

noncomputable def plan {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :=
  IntegralMixedEmptyUnitPlan.plan (parameters n t) (originals hn ht ha)
    (ambient_positive n t) (auxiliary_cap n t) (room n t)

noncomputable def data {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :=
  IntegralMixedEmptyUnitPlan.data (parameters n t) (originals hn ht ha)
    (ambient_positive n t) (auxiliary_cap n t) (room n t) (source_width n t)

theorem source_geometry {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root)
    (root : List Bool) (birth : ℕ) :
    IntegralMixedCanonicalUnitSourceBits.source (parameters n t) (originals hn ht ha) root birth =
      LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.source (frozen n root birth) (degreeCharge n t root) (t root)
        (augmented n t root).degreeBound_le_dataSize birth (scalarWidth n t root) (height n t root birth) := by
  rw [IntegralMixedCanonicalTiltedSourceBits.source_originals]
  exact IntegralMixedCanonicalTiltedSourceBits.source_geometry (frozen n root birth)
    (levelExponent n t root birth) (Fin.last (n root)) (augmented n t root)

private theorem recursive_height_eq (N S B D C j : ℕ) :
    LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.recursiveHeight N S B D C j =
      IntegralMixedFramedStepHeight.height (N+2) S B (FixedLeadingTiltedSource.degree D).size
        (FixedLeadingTiltedSource.degree D) 1
        (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.sourceFactor N S B D+2) C j := by
  rw [LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.recursiveHeight_eq_scheduled]
  unfold LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.scheduledHeight IntegralMixedFramedStepHeight.height
  simp only [LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.nextHeight,Nat.mul_one]

theorem height_eq {n : List Bool → ℕ} {t : List Bool → Term} (root : List Bool) (birth : ℕ) :
    height n t root birth = IntegralMixedFramedStepHeight.height ((parameters n t).ambient root)
      ((parameters n t).cap root+1) ((parameters n t).width root) ((parameters n t).sourceWidth root)
      ((parameters n t).degree root) 1 (factor n t root) (seed n t root) birth := by
  simpa only [height,parameters,spatialDegree,factor,stateHorizon] using
    recursive_height_eq (n root) (stateHorizon n root) (scalarWidth n t root)
      (degreeCharge n t root) (seed n t root) birth
end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
