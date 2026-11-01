/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalDispatcher
public import LeanCanny.Algebra.IntegralMixedVirtualContextDispatcher
/-! # Critical arithmetic has no retained-generator companion phase -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCriticalPhaseBoundary
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem physical (P : Parameters) (a : Access P) (F : IntegralMixedPhysicalCriticalBits.Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (ha : SpaceFunction (IntegralMixedPhysicalNativeLowerBits.originalScalar P F))
    (q : List Bool) (hp : phase q = 26) : (IntegralMixedPhysicalDispatcherBits.machine P a F h ha).model q = [] := by
  change (if IntegralMixedPhysicalDispatcherBits.lowerSelected q then _ else
    (IntegralMixedPhysicalUpperDispatcherBits.machine P a F h).model q) = []
  have hs : IntegralMixedPhysicalDispatcherBits.lowerSelected q = false := by
    apply decide_eq_false
    omega
  rw [hs, ite_eq_right (by decide), IntegralMixedPhysicalUpperDispatcherBits.machine_model]
  simp only [IntegralMixedPhysicalUpperBits.selectedFinite, IntegralMixedPhysicalUpperBits.selected,
    IntegralMixedPhysicalContextBits.selected, isPhase, hp, Phase.code, Nat.reduceEqDiff,
    and_false, false_and, decide_false, Bool.false_and, Bool.cond_false]

theorem virtual (P : Parameters) (a : Access P) (F : IntegralMixedCutSource.Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (ha : SpaceFunction (IntegralMixedVirtualNativeLowerBits.originalScalar P F))
    (q : List Bool) (hp : phase q = 26) : (IntegralMixedVirtualContextDispatcherBits.machine P a F h ha).model q = [] := by
  change (if IntegralMixedVirtualContextDispatcherBits.lowerSelected q then _ else
    (IntegralMixedVirtualContextUpperDispatcherBits.machine P a F h).model q) = []
  have hs : IntegralMixedVirtualContextDispatcherBits.lowerSelected q = false := by
    apply decide_eq_false
    omega
  rw [hs, ite_eq_right (by decide), IntegralMixedVirtualContextUpperDispatcherBits.machine_model]
  simp only [IntegralMixedVirtualContextUpperBits.selectedFinite, IntegralMixedVirtualContextUpperBits.selected,
    IntegralMixedVirtualContextBits.selected, isPhase, hp, Phase.code, Nat.reduceEqDiff,
    and_false, false_and, decide_false, Bool.false_and, Bool.cond_false]

end LeanCanny.Algebra.IntegralMixedCriticalPhaseBoundary
