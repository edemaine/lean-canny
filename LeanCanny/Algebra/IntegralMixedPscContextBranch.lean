/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscContextUpperCorrect
public import LeanCanny.Algebra.IntegralMixedPscEntryScoped
/-! # A joinable native PSC branch occupies only determinant phases zero to four -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscContextBranchBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical

def InScope (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralMixedPscContextUpperBits.Domain P F q ∧ phase q ≤ 4
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (InScope P F q) := inferInstanceAs (Decidable (_ ∧ _))
theorem scope_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (InScope P F) :=
  (IntegralMixedPscContextUpperBits.domain_FP P a F h).and
    ((BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27)).le (BinaryFn.const 4))

noncomputable def branch (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  (IntegralMixedPscContextUpperDispatcher.machine P a F h).withGuard
    (fun q => decide (InScope P F q)) (scope_FP P a F h).flag_mem_FP

theorem branch_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (branch P a F h).selected q = true ↔ InScope P F q := by
  change decide (InScope P F q) = true ↔ _
  simp only [decide_eq_true_eq]

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (entries : IntegralMixedPscContextActionBits.EntryMatches P F (fun q => residueBits (x q)))
    (own : IntegralMixedPscContextUpperModel.Matches P F (fun q => residueBits (x q))) :
    Correct (branch P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  withGuard_correct _ _ _ _ _ (IntegralMixedPscContextUpperDispatcher.correct P a F h g x entries own)
    (fun q _ => IntegralMixedPscContextUpperDispatcher.machine_selected P a F h q)

theorem model_component (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool)
    (hq : InScope P F q) :
    (branch P a F h).model q = IntegralMixedPscContextUpperModel.component P F (phase q) q := by
  change (IntegralMixedPscContextUpperDispatcher.machine P a F h).model q = _
  rw [IntegralMixedPscContextUpperDispatcher.machine_model]
  exact IntegralMixedPscContextUpperModel.value_phase P F q (phase q) (by have HP := hq.2; omega) hq.1 rfl

theorem canonical (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (branch P a F h).model q :=
  IntegralMixedPscContextUpperDispatcher.canonical P a F h q

theorem branch_not_gram (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool)
    (hp : 19 ≤ phase q) : (branch P a F h).selected q = false := by
  cases hs : (branch P a F h).selected q with
  | false => rfl
  | true => have H := ((branch_selected P a F h q).mp hs).2; omega

abbrev CurrentMatches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, InScope P F q → answer q = (branch P a F h).model q

theorem matches_of_current (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool) (own : CurrentMatches P a F h answer) :
    IntegralMixedPscContextUpperModel.Matches P F answer := by
  intro q hq hp
  have Hscope : InScope P F q := ⟨hq, by omega⟩
  exact (own q Hscope).trans (model_component P a F h q Hscope)

theorem entries_of_scoped_current (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool)
    (own : ∀ q, IntegralMixedPscEntryScopedBits.Selected P F q →
      answer q = (IntegralMixedPscEntryScopedBits.machine P a F h).model q) :
    IntegralMixedPscContextActionBits.EntryMatches P F answer := by
  intro q hq
  exact own q hq

theorem correct_of_current (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (entries : IntegralMixedPscContextActionBits.EntryMatches P F (fun q => residueBits (x q)))
    (own : CurrentMatches P a F h (fun q => residueBits (x q))) :
    Correct (branch P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h g x entries (matches_of_current P a F h _ own)

end LeanCanny.Algebra.IntegralMixedPscContextBranchBits
