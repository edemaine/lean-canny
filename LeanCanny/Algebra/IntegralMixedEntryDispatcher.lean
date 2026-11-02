/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueRowScopedCurrent
public import LeanCanny.Algebra.IntegralMixedPscEntryScoped
/-! # Routine two dispatches PSC entries and virtual value-row entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedEntryDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  (IntegralMixedPscEntryScopedBits.machine P a F h).choose (IntegralMixedValueRowScopedBits.machine P a F h)

theorem model_psc_all (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool)
    (hq : IntegralMixedPscEntryScopedBits.Selected P F q) : (machine P a F h).model q = IntegralMixedPscEntryBits.value P F q := by
  change (if decide (IntegralMixedPscEntryScopedBits.Selected P F q) then _ else _) = _
  rw [ite_eq_left (decide_eq_true hq)]
  rfl

theorem model_psc (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool)
    (hq : IntegralMixedPscEntryBits.Selected P F q) : (machine P a F h).model q = IntegralMixedPscEntryBits.value P F q := by
  apply model_psc_all P a F h q
  refine ⟨hq.1, hq.2.1, hq.2.2.1, ?_, hq.2.2.2.2⟩
  unfold IntegralMixedVirtualContextBits.context
  have HX := hq.2.2.2.1
  omega

theorem model_row (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool)
    (hq : IntegralMixedValueRowScopedBits.InScope P q) :
    (machine P a F h).model q = (IntegralMixedValueRowScopedBits.machine P a F h).model q := by
  have HN : ¬IntegralMixedPscEntryScopedBits.Selected P F q := by
    intro HP
    have HE : phase q = 0 := HP.2.2.1
    have HL := hq.2.1
    omega
  change (if decide (IntegralMixedPscEntryScopedBits.Selected P F q) then _ else _) = _
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using HN)]

theorem selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (machine P a F h).selected q = true := by
  change (_ || (IntegralMixedValueRowScopedBits.machine P a F h).selected q) = true
  rw [IntegralMixedValueRowScopedBits.machine_selected, Bool.or_true]

theorem canonical (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a F h).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    if decide (IntegralMixedPscEntryScopedBits.Selected P F q) then IntegralMixedPscEntryBits.value P F q else (IntegralMixedValueRowScopedBits.machine P a F h).model q
  split_ifs
  · exact ⟨_, rfl⟩
  · exact IntegralMixedValueRowScopedBits.canonical P a F h q

abbrev Matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (answer : List Bool → List Bool) : Prop :=
  ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 2 → answer q = (machine P a F h).model q

theorem row_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool) (hm : Matches P a F h answer) : IntegralMixedValueRowScopedBits.CurrentMatches P a F h answer := by
  intro q hq
  exact (hm q hq.1.1 hq.1.2.1).trans (model_row P a F h q hq)

theorem psc_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool) (hm : Matches P a F h answer) (q : List Bool)
    (hq : IntegralMixedPscEntryBits.Selected P F q) : answer q = IntegralMixedPscEntryBits.value P F q :=
  (hm q hq.1 hq.2.1).trans (model_psc P a F h q hq)

theorem psc_matches_all (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool) (hm : Matches P a F h answer) (q : List Bool)
    (hq : IntegralMixedPscEntryScopedBits.Selected P F q) : answer q = IntegralMixedPscEntryBits.value P F q :=
  (hm q hq.1 hq.2.1).trans (model_psc_all P a F h q hq)

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : RootGeometry P F)
    (answer : List Bool → List Bool) (hm : Matches P a F h answer)
    (he : IntegralMixedValueRowScopedBits.External P F answer)
    (hv : IntegralMixedVirtualContextComponentBits.Matches P F answer) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  choose_correct _ _ _ _ (IntegralMixedPscEntryScopedBits.correct_of_matches P a F h g answer hv)
    (IntegralMixedValueRowScopedBits.correct_of_current P a F h g answer he (row_matches P a F h answer hm))
end LeanCanny.Algebra.IntegralMixedEntryDispatcherBits
