/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramScoped
public import LeanCanny.Algebra.IntegralMixedEntryDispatcher
/-! # Gram current replies close against scoped routine-two entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramScopedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
set_option backward.isDefEq.respectTransparency false

abbrev CurrentMatches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (answer : List Bool → List Bool) : Prop :=
  ∀ q, InScope P q → answer q = (machine P a F h).model q

theorem matches_of_current (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool) (hm : CurrentMatches P a F h answer) : Matches P F answer := by
  intro q hv hr hp hx
  have HQ : InScope P q := ⟨⟨hv, hr, hx⟩, hp⟩
  exact (hm q HQ).trans (model_component P a F h q HQ)

theorem rows_of_entries (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool) (hm : IntegralMixedEntryDispatcherBits.Matches P a F h answer) : Rows P F answer :=
  IntegralMixedValueRowScopedBits.matches_of_current P a F h answer (IntegralMixedEntryDispatcherBits.row_matches P a F h answer hm)

theorem correct_of_current (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q)) (hr : Rows P F (fun q => residueBits (x q)))
    (hm : CurrentMatches P a F h (fun q => residueBits (x q))) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h g x hr (matches_of_current P a F h _ hm)

theorem correct_of_entries (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hr : IntegralMixedEntryDispatcherBits.Matches P a F h (fun q => residueBits (x q)))
    (hm : CurrentMatches P a F h (fun q => residueBits (x q))) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct_of_current P a F h g x (rows_of_entries P a F h _ hr) hm

theorem machine_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (machine P a F h).selected q = true := by
  change (_ || true) = true
  exact Bool.or_true _

theorem model_physical_context (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool)
    (hx : get P .slot15 q = 1) : (machine P a F h).model q = [] :=
  model_outside P a F h q (fun HQ => by have := HQ.1.2.2.1; omega)

theorem model_psc_phase (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool)
    (hp : phase q ≤ 4) : (machine P a F h).model q = [] :=
  model_outside P a F h q (fun HQ => by have H := HQ.2; unfold PhaseAllowed at H; omega)

theorem branch_not_psc (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool)
    (hp : phase q ≤ 4) : (branch P a F h).selected q = false := by
  cases hs : (branch P a F h).selected q with
  | false => rfl
  | true =>
    have H := ((branch_selected P a F h q).mp hs).2
    unfold PhaseAllowed at H
    omega

theorem model_phase (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : ℕ) (q : List Bool)
    (hq : InScope P q) (hp : phase q = p) : (machine P a F h).model q = IntegralMixedGramUpperModel.component P F p q :=
  (model_component P a F h q hq).trans (congrArg (fun n => IntegralMixedGramUpperModel.component P F n q) hp)
end LeanCanny.Algebra.IntegralMixedGramScopedBits
