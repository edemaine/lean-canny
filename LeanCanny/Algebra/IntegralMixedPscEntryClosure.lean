/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscEntryNative
public import LeanCanny.Algebra.IntegralMixedVirtualContextComponent
/-! # The actual PSC entry closes against current mixed critical replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource
open scoped Classical

theorem child_selected (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hs : Selected P F q) (hr : Request P F q) :
    IntegralMixedVirtualContextBits.selected P .criticalCoefficient (query P F q) = true := by
  apply decide_eq_true
  refine ⟨?_, IntegralMixedValueFieldQuery.query_routine P id .critical .criticalCoefficient .coefficient _ q,
    IntegralMixedValueFieldQuery.query_phase P id .critical .criticalCoefficient .coefficient _ q, ?_⟩
  · unfold IntegralMixedVirtualCaps.valid
    rw [query_root, query_birth]
    exact hs.1
  · have HC : get P .slot15 (query P F q) = 3 := by
      simpa only [query_get P F g q hr, reduceCtorEq, ite_false] using hs.2.2.2.1
    unfold IntegralMixedVirtualContextBits.context
    rw [HC]
    decide

theorem replies_of_matches (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (own : IntegralMixedVirtualContextComponentBits.Matches P F answer)
    (q : List Bool) (hs : Selected P F q) : RepliesAt P F answer q := by
  intro hr
  have H := own .criticalCoefficient (query P F q) (by decide) (child_selected P F g q hs hr)
  change answer (query P F q) = (IntegralMixedVirtualTaskBits.source P F).value (query P F q) at H
  exact H

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (own : IntegralMixedVirtualContextComponentBits.Matches P F answer) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h g answer (fun q hs => replies_of_matches P F g answer own q hs)

end LeanCanny.Algebra.IntegralMixedPscEntryBits
