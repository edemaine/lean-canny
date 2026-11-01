/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscActionMachine
/-! # PSC determinant entries close against the actual lower PSC branch -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedPscActionTasks
open scoped Classical

abbrev EntryMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedPscEntryBits.Selected P F q → answer q = IntegralMixedPscEntryBits.value P F q

theorem child_selected (P : Parameters) (F : Family) (q : List Bool)
    (hs : IntegralMixedPscUpperBits.selected P F .originalCoefficient q = true) :
    IntegralMixedPscEntryBits.Selected P F (query P F q) := by
  have HH := (IntegralMixedPscUpperBits.selected_iff P F .originalCoefficient q).mp hs
  refine ⟨?_, IntegralMixedValueFieldQuery.query_routine P (third P F) .pscEntry .originalCoefficient .col _ q,
    IntegralMixedValueFieldQuery.query_phase P (third P F) .pscEntry .originalCoefficient .col _ q, ?_, ?_⟩
  · unfold IntegralMixedVirtualCaps.valid
    rw [query_root, query_birth]
    exact HH.1.1
  · simpa only [query_get, reduceCtorEq, ite_false] using HH.1.2.2.1
  · have HD : IntegralMixedPscEntryBits.degree P F (query P F q) = IntegralMixedPscEntryBits.degree P F q := by
      change IntegralMixedCoordinateSquarefree.coordinateDegree
        (F.spatial (IntegralMixedVirtualTaskBits.saved P (query P F q)))
        (F.rule (IntegralMixedVirtualTaskBits.saved P (query P F q))) = _
      rw [query_saved]
      rfl
    rw [HD]
    simpa only [query_get, reduceCtorEq, ite_false] using HH.1.2.2.2

theorem replies_of_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (own : EntryMatches P F answer) (q : List Bool)
    (hs : IntegralMixedPscUpperBits.selected P F .originalCoefficient q = true) : RepliesAt P F answer q :=
  own _ (child_selected P F q hs)

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (answer : List Bool → List Bool) (own : EntryMatches P F answer) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h answer (fun q hs => replies_of_matches P F answer own q hs)

end LeanCanny.Algebra.IntegralMixedPscActionBits
