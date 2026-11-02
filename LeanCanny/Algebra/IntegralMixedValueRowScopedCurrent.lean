/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueRowScoped
/-! # Value-row current matches are restricted to the same virtual context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueRowScopedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
set_option backward.isDefEq.respectTransparency false

abbrev CurrentMatches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (answer : List Bool → List Bool) : Prop :=
  ∀ q, InScope P q → answer q = (machine P a F h).model q

theorem matches_of_current (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool) (hm : CurrentMatches P a F h answer) : Matches P F answer := by
  intro q hv hr hlo hhi hx
  have HQ : InScope P q := ⟨⟨hv, hr, hx⟩, hlo, hhi⟩
  exact (hm q HQ).trans (model_component P a F h q HQ)

theorem correct_of_current (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : RootGeometry P F)
    (answer : List Bool → List Bool) (he : External P F answer) (hm : CurrentMatches P a F h answer) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h g answer he (matches_of_current P a F h answer hm)

theorem model_physical_context (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool)
    (hx : get P .slot15 q = 1) : (machine P a F h).model q = [] :=
  model_outside P a F h q (fun HQ => by have := HQ.1.2.2.1; omega)

theorem model_psc_phase (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool)
    (hp : phase q = 0) : (machine P a F h).model q = [] :=
  model_outside P a F h q (fun HQ => by have := HQ.2.1; omega)

theorem branch_not_psc (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool)
    (hp : phase q = 0) : (branch P a F h).selected q = false := by
  cases hs : (branch P a F h).selected q with
  | false => rfl
  | true => have H := ((branch_selected P a F h q).mp hs).2.1; omega

theorem model_phase (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : ℕ) (q : List Bool)
    (hq : InScope P q) (hp : phase q = p) :
    (machine P a F h).model q = IntegralMixedValueRowModel.component P F p q :=
  (model_component P a F h q hq).trans (congrArg (fun n => IntegralMixedValueRowModel.component P F n q) hp)
end LeanCanny.Algebra.IntegralMixedValueRowScopedBits
