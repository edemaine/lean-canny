/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptySourceBounds
/-! # Original syntax supplies every instruction bound of the empty plan

The chronological source bounds are charged at their actual scalar births.
The default instruction uses source0 and the original seed. Thus arbitrary
record choices need no supplied script, prefix LOW or interpreted bank bound.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedStepHeight
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root)

theorem script_bounds (root : List Bool) :
    ScriptBounds ((parameters n t).cap root+1) ((parameters n t).sourceWidth root) ((parameters n t).degree root)
      1 (factor n t root) (seed n t root) ((plan hn ht ha).rules root) := by
  change ScriptBounds _ _ _ _ _ _ (((List.range (IntegralMixedEmptyUnitPlan.count root)).map
    (IntegralMixedEmptyUnitPlan.step (parameters n t) (originals hn ht ha) (ambient_positive n t) (auxiliary_cap n t) root)).reverse)
  apply IntegralMixedEmptyInstructionBounds.reverse_range_bounds
  intro birth hb
  have hcount : birth<recordCount root := hb
  have hB : birth≤stateHorizon n root := by
    change birth≤max (n root) (recordCount root)+2+1
    have H:=le_max_right (n root) (recordCount root)
    omega
  have H := step_bounds hn ht ha root birth hB
  rw [height_eq] at H
  exact H

theorem default_bounds (root : List Bool) :
    InstructionBounds (seed n t root+1) (factor n t root) ((parameters n t).sourceWidth root)
      ((parameters n t).degree root) 1
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction (parameters n t) (plan hn ht ha) root) := by
  change InstructionBounds (height n t root 0) _ _ _ _ _
  apply source_instruction_bounds hn ht ha root 0 (Nat.zero_le _) _ rfl
  change ∀ j : ℕ, ((Polynomial.X : Polynomial ℤ).coeff j).natAbs ≤
    2^(factor n t root*height n t root 0+1)
  intro j
  rw [Polynomial.coeff_X]
  split_ifs
  · exact Nat.one_le_two_pow
  · exact Nat.zero_le _

theorem familyInputs : FamilyInputs (parameters n t) (plan hn ht ha) (fun _ => 1) (factor n t) (seed n t) where
  script := script_bounds hn ht ha
  default := default_bounds hn ht ha
end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
