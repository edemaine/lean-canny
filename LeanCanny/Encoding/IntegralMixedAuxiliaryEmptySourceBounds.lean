/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
public import LeanCanny.Encoding.IntegralMixedEmptyInstructionBounds
public import LeanCanny.Algebra.IntegralMixedFramedUnitSourceBounds
/-! # Actual empty-plan sources obey the derived original causal bounds -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedStepHeight
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root)

attribute [local irreducible] degreeCharge spatialDegree scalarCeiling scalarWidth IntegralMixedAuxiliarySchedule.height factor seed levelExponent
attribute [local irreducible] IntegralMixedCanonicalTiltedSourceBits.originals description

theorem source_instruction_bounds (root : List Bool) (birth : ℕ) (hb : birth≤stateHorizon n root)
    (I : Instruction ((parameters n t).ambient root) ((parameters n t).width root))
    (hI : I.source=IntegralMixedCanonicalUnitSourceBits.source (parameters n t) (originals hn ht ha) root birth)
    (hc : IntegralMixedFullScriptHeight.CommandBounds
      (factor n t root*height n t root birth+1) 1 I.command) :
    InstructionBounds (height n t root birth) (factor n t root) ((parameters n t).sourceWidth root)
      ((parameters n t).degree root) 1 I := by
  have hG := IntegralMixedAuxiliarySchedule.height_positive n t root birth
  have hWord := word_le_height n t root birth
  have hE := LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.source_exponent_bound
    (n:=n root) (D:=degreeCharge n t root) (B:=scalarWidth n t root) hb hG
  have hAux : IntegralMixedExceptionalBounds.auxiliaryCap (n root+3) (spatialDegree n t root)≤2^scalarWidth n t root :=
    auxiliary_cap n t root
  have hCap : PurePowerReductionBounds.dimension (n root+3) (spatialDegree n t root)≤2^scalarWidth n t root :=
    (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
      PurePowerReductionBounds.dimension (n root+3) (spatialDegree n t root)≤
        IntegralMixedExceptionalBounds.auxiliaryCap (n root+3) (spatialDegree n t root)).trans hAux
  have hM : spatialDegree n t root=FixedLeadingTiltedSource.degree (degreeCharge n t root) := by
    unfold spatialDegree
    rfl
  rw [hM] at hCap hAux
  have hWidth : (FixedLeadingTiltedSource.degree (degreeCharge n t root)).size≤(parameters n t).sourceWidth root := by
    change _≤(spatialDegree n t root).size
    rw [hM]
  have hDegree : FixedLeadingTiltedSource.degree (degreeCharge n t root)≤(parameters n t).degree root := by
    change _≤spatialDegree n t root
    rw [hM]
  have hTerm : (augmented n t root).degreeBound≤degreeCharge n t root := by
    unfold degreeCharge
    exact (augmented n t root).degreeBound_le_dataSize
  have hExp : levelExponent n t root birth≤
      LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.sourceFactor (n root) (stateHorizon n root)
        (scalarWidth n t root) (degreeCharge n t root)*height n t root birth := by
    simpa only [levelExponent] using hE
  have H := IntegralMixedFramedUnitSourceBounds.tilted_default_bounds
    (n:=n root+1) (k:=frozen n root birth) (D:=degreeCharge n t root)
    (T:=(FixedLeadingTiltedSource.lowTerm (frozen n root birth) (degreeCharge n t root) (n root) (augmented n t root)).toData.size)
    (E:=levelExponent n t root birth)
    (f:=LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.sourceFactor (n root) (stateHorizon n root)
      (scalarWidth n t root) (degreeCharge n t root))
    (G:=height n t root birth) (B:=scalarWidth n t root)
    (W:=(parameters n t).sourceWidth root) (D':=(parameters n t).degree root) (L:=1)
    (Fin.last (n root)) (augmented n t root) hTerm
    hCap (Nat.le_refl _) hG hWord hExp hWidth hDegree hAux
  unfold factor at hc ⊢
  refine ⟨?_,?_,?_,?_,?_,hc⟩
  · intro e
    rw [hI,source_geometry hn ht ha root birth]
    simpa only [LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.source,
      LeanCanny.Geometry.IntegralMixedCausalLevelCapacity.coefficient,levelExponent,augmented,degreeCharge,parameters,Nat.add_assoc] using H.low e
  · rw [hI,source_geometry hn ht ha root birth]
    exact H.leading
  · rw [hI,source_geometry hn ht ha root birth]
    exact H.width
  · rw [hI,source_geometry hn ht ha root birth]
    exact H.degree
  · rw [hI,source_geometry hn ht ha root birth]
    exact H.auxiliary

theorem step_bounds (root : List Bool) (birth : ℕ) (hb : birth≤stateHorizon n root) :
    InstructionBounds (height n t root birth) (factor n t root) ((parameters n t).sourceWidth root)
      ((parameters n t).degree root) 1
      (IntegralMixedEmptyUnitPlan.step (parameters n t) (originals hn ht ha)
        (ambient_positive n t) (auxiliary_cap n t) root birth) := by
  apply source_instruction_bounds hn ht ha root birth hb _ rfl
  change IntegralMixedFullScriptHeight.CommandBounds _ 1
    (IntegralMixedCanonicalUnitRuleBits.command
      (IntegralMixedCanonicalUnitSourceBits.source (parameters n t) (originals hn ht ha) root birth)
      (ambient_positive n t root) birth (IntegralMixedEmptyUnitPlan.code root birth) (auxiliary_cap n t root))
  exact IntegralMixedEmptyInstructionBounds.command_bounds
    (n:=(parameters n t).ambient root) (B:=(parameters n t).width root)
    (IntegralMixedCanonicalUnitSourceBits.source (parameters n t) (originals hn ht ha) root birth)
    (ambient_positive n t root) birth (IntegralMixedEmptyUnitPlan.code root birth) (auxiliary_cap n t root)
    (factor n t root*height n t root birth+1) (Nat.le_add_left 1 _)
end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
