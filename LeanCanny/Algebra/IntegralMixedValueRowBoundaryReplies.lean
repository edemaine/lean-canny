/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueRowInternalReplies

/-! # Exact existing lower-routine boundaries for the actual row dispatcher -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueRowBoundaryReplies
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualCaps IntegralMixedValueRowInternalReplies
open scoped Classical

structure External (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop where
  frozen : ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → phase q = 12 →
    answer q = IntegralMixedVirtualSnapshotBits.frozenLower P F q
  gradient : ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → phase q = 8 →
    answer q = IntegralMixedVirtualSpatialBits.cleared P F q
  critical : ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → phase q = 25 →
    answer q = (IntegralMixedVirtualTaskBits.source P F).value q
  originalScale : ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 0 → phase q = 5 →
    answer q = IntegralMixedOriginalScaleBits.value P F q
  commonLeading : ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 0 → phase q = 3 →
    answer q = IntegralCriticalLeadingBits.value (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen q

theorem task_valid (P : Parameters) (F : Family) (q : List Bool) (hv : valid P q) (p : Phase) (x : ℕ) :
    valid P (IntegralMixedFullRowTasks.taskAt P F p x q) :=
  valid_transport P q _ hv (IntegralMixedFullRowTasks.task_root P F p x q) (IntegralMixedFullRowTasks.task_birth P F p x q)
theorem task_routine (P : Parameters) (F : Family) (q : List Bool) (p : Phase) (x : ℕ) :
    IntegralMixedRoutineTaskBits.routine P (IntegralMixedFullRowTasks.taskAt P F p x q) = 1 :=
  IntegralMixedValueFieldQuery.query_routine P (IntegralMixedFullRowTasks.targetTask P F p) .critical p .expression (fun _ => x) q
theorem task_phase (P : Parameters) (F : Family) (q : List Bool) (p : Phase) (x : ℕ) :
    phase (IntegralMixedFullRowTasks.taskAt P F p x q) = p.code :=
  IntegralMixedValueFieldQuery.query_phase P (IntegralMixedFullRowTasks.targetTask P F p) .critical p .expression (fun _ => x) q
theorem scalar_valid (P : Parameters) (q : List Bool) (hv : valid P q) (p : Phase) :
    valid P (IntegralMixedRoutineTaskBits.query P (birth P) .scalar p q) :=
  valid_transport P q _ hv (IntegralMixedRoutineTaskBits.query_root P (birth P) .scalar p q)
    (IntegralMixedRoutineTaskBits.query_birth P (birth P) .scalar p q (min_le_right _ _))

theorem fullrow (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (he : External P F answer) (q : List Bool) (hv : valid P q) :
    IntegralMixedFullRowBranch.RepliesAt P F answer q := by
  by_cases HE : IntegralMixedFullRowTasks.equation P F q
  · constructor
    · simp only [IntegralMixedFullRowLowerChild.model, IntegralMixedFullRowTasks.lowTask, HE, ite_true]
      exact he.frozen _ (task_valid P F q hv .frozenLower 0) (task_routine P F q .frozenLower 0)
        (task_phase P F q .frozenLower 0)
    · simp only [IntegralMixedFullRowScalarChild.model, IntegralMixedFullRowTasks.scalarTask, HE, ite_true]
      exact he.originalScale _ (scalar_valid P q hv .productEntry)
        (IntegralMixedRoutineTaskBits.query_routine P (birth P) .scalar .productEntry q)
        (IntegralMixedRoutineTaskBits.query_phase P (birth P) .scalar .productEntry q)
  · constructor
    · simp only [IntegralMixedFullRowLowerChild.model, IntegralMixedFullRowTasks.lowTask, HE, ite_false]
      exact he.gradient _ (task_valid P F q hv .clearedGridSum 1) (task_routine P F q .clearedGridSum 1)
        (task_phase P F q .clearedGridSum 1)
    · simp only [IntegralMixedFullRowScalarChild.model, IntegralMixedFullRowTasks.scalarTask, HE, ite_false]
      exact he.commonLeading _ (scalar_valid P q hv .monomialFactor)
        (IntegralMixedRoutineTaskBits.query_routine P (birth P) .scalar .monomialFactor q)
        (IntegralMixedRoutineTaskBits.query_phase P (birth P) .scalar .monomialFactor q)

theorem homogeneous (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (he : External P F answer) (own : IntegralMixedValueRowModel.Matches P F answer) (q : List Bool) (hv : valid P q) :
    IntegralMixedValueHomogeneousPoint.RepliesAt P F answer q := by
  intro _
  by_cases HE : get P .slot8 q = 0
  · simp only [IntegralMixedValueHomogeneousPoint.currentValue, IntegralMixedValueHomogeneousQueries.query, HE, ite_true]
    exact homogeneous_original P F answer own q hv
  · simp only [IntegralMixedValueHomogeneousPoint.currentValue, IntegralMixedValueHomogeneousQueries.query, HE, ite_false]
    apply he.critical
    · exact valid_transport P q _ hv (IntegralMixedValueHomogeneousQueries.coordinateTask_root P F q)
        (IntegralMixedValueHomogeneousQueries.coordinateTask_birth P F q)
    · exact IntegralMixedValueFieldQuery.query_routine P (IntegralMixedValueHomogeneousQueries.coordinateBase P)
        .critical .criticalCoefficient .coefficient (IntegralMixedValueHomogeneousQueries.coordinateCoefficient P F) q
    · exact IntegralMixedValueFieldQuery.query_phase P (IntegralMixedValueHomogeneousQueries.coordinateBase P)
        .critical .criticalCoefficient .coefficient (IntegralMixedValueHomogeneousQueries.coordinateCoefficient P F) q

end LeanCanny.Algebra.IntegralMixedValueRowBoundaryReplies
