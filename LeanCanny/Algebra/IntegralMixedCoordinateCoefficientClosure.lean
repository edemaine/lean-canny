/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCoordinateCoefficientNative
/-! # The raw coordinate kernel closes against current virtual critical replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCoordinateCoefficientNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedCoordinateCoefficientTasks
open IntegralMixedValueCoefficientTasks (Labels)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem child_selected (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hs : Selected P F q) (hl : Labels P F q) :
    IntegralMixedVirtualContextBits.selected P .criticalCoefficient (query P F q) = true := by
  apply decide_eq_true
  refine ⟨?_, query_routine P F q, query_phase P F q, ?_⟩
  · unfold IntegralMixedVirtualCaps.valid
    rw [query_root, query_birth]
    exact hs.1
  · unfold IntegralMixedVirtualContextBits.context
    simp only [query_get P F g q hs.1 hl, reduceCtorEq, ite_false]
    exact hs.2.2.2.2

theorem replies_of_matches (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (own : IntegralMixedVirtualContextComponentBits.Matches P F answer)
    (q : List Bool) (hs : Selected P F q) : RepliesAt P F answer q := by
  intro hl
  have he := own .criticalCoefficient (query P F q) (by decide) (child_selected P F g q hs hl)
  change answer (query P F q) = (IntegralMixedVirtualTaskBits.source P F).value (query P F q) at he
  exact he

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool)
    (own : IntegralMixedVirtualContextComponentBits.Matches P F answer) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h g answer (fun q hs => replies_of_matches P F g answer own q hs)

end LeanCanny.Algebra.IntegralMixedCoordinateCoefficientNative
