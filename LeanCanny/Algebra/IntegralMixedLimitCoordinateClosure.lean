/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateNative
/-! # Current virtual critical replies close the last limit-coordinate request -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinateNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open IntegralMixedValueCoefficientTasks (Labels)
open scoped Classical

theorem prepared_selected (P : Parameters) (F : Family) (q : List Bool) (hs : Selected P F q) :
    IntegralMixedCoordinateCoefficientNative.Selected P F (IntegralMixedLimitCoordinateTasks.prepare P q) := by
  refine ⟨(IntegralMixedLimitCoordinateTasks.prepare_valid P q).mpr hs.1,
    IntegralMixedLimitCoordinateTasks.prepare_routine P q, IntegralMixedLimitCoordinateTasks.prepare_phase P q, ?_, ?_⟩
  · rw [IntegralMixedLimitCoordinateTasks.prepare_get, IntegralMixedLimitCoordinateValue.choiceBound_prepare]
    exact hs.2.2.2.2.2.1.trans_lt hs.2.2.2.2.1
  · unfold IntegralMixedVirtualContextBits.context
    simp only [IntegralMixedLimitCoordinateTasks.prepare_get, reduceCtorEq, ite_false]
    exact hs.2.2.2.1

theorem child_selected (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hs : Selected P F q) :
    IntegralMixedVirtualContextBits.selected P .criticalCoefficient (IntegralMixedLimitCoordinateTasks.critical P F q)=true :=
  IntegralMixedCoordinateCoefficientNative.child_selected P F g (IntegralMixedLimitCoordinateTasks.prepare P q)
    (prepared_selected P F q hs) hs.2.2.2.2.2.2

theorem replies_of_matches (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (R : Routing) (answer : List Bool → List Bool) (own : IntegralMixedVirtualContextComponentBits.Matches P F answer)
    (q : List Bool) (hs : Selected P F q) (bank : IntegralMixedOldBankCofactorBits.RepliesAt P F R answer q) :
    IntegralMixedLimitCoordinateValue.RepliesAt P F R answer q := by
  refine ⟨bank, ?_⟩
  have H := own .criticalCoefficient (IntegralMixedLimitCoordinateTasks.critical P F q) (by decide) (child_selected P F g q hs)
  exact H

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (R : Routing) (hr : RoutingAccess R)
    (answer : List Bool → List Bool) (own : IntegralMixedVirtualContextComponentBits.Matches P F answer)
    (bank : ∀ q, Selected P F q → IntegralMixedOldBankCofactorBits.RepliesAt P F R answer q) :
    Correct (machine P a F h R hr) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h g R hr answer (fun q hs => replies_of_matches P F g R answer own q hs (bank q hs))

end LeanCanny.Algebra.IntegralMixedLimitCoordinateNative
