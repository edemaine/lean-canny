/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueRowContextPatch
public import LeanCanny.Algebra.IntegralMixedRoutineContextGuard
/-! # Value-row arithmetic has only virtual-context current callbacks -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueRowScopedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedValueRowDispatcher.machine

def InScope (P : Parameters) (q : List Bool) : Prop :=
  IntegralMixedRoutineContextGuard.Selected P 2 2 4 q ∧ 21 ≤ phase q ∧ phase q ≤ 26

theorem selected_FP (P : Parameters) (a : Access P) : FPPred (InScope P) :=
  (IntegralMixedRoutineContextGuard.selected_FP P a 2 2 4).and
    (((BinaryFn.const 21).le (BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27))).and
      ((BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27)).le (BinaryFn.const 26)))

noncomputable def branch (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  (IntegralMixedValueRowDispatcher.machine P a F h).withGuard (fun q => decide (InScope P q)) (selected_FP P a).flag_mem_FP
noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  (branch P a F h).choose zero

theorem branch_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : RootGeometry P F)
    (answer : List Bool → List Bool) (he : External P F answer) (hm : Matches P F answer) :
    Correct (branch P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  have HY := IntegralMixedValueRowDispatcher.correct P a F h g (patch P F answer)
    (patch_external P F answer he) (patch_matches P F answer hm)
  apply withGuard_oracle_correct _ _ _ (patch P F answer) answer _ HY
  · intro q _
    exact IntegralMixedValueRowDispatcher.machine_selected P a F h q
  · intro q hq budget c hreq
    have HQ : InScope P q := of_decide_eq_true hq
    have HE := IntegralMixedValueRowContextBits.requests_context P a F h (patch P F answer)
      q (IntegralMixedValueRowDispatcher.machine_selected P a F h q) budget c hreq
    have HX : IntegralMixedVirtualContextBits.context P c := by
      unfold IntegralMixedVirtualContextBits.context
      rw [show get P .slot15 c = get P .slot15 q from HE]
      exact HQ.1.2.2
    exact patch_good P F answer c HX

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : RootGeometry P F)
    (answer : List Bool → List Bool) (he : External P F answer) (hm : Matches P F answer) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  choose_correct _ _ _ _ (branch_correct P a F h g answer he hm) (zero_correct _ _)

theorem branch_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (branch P a F h).selected q = true ↔ InScope P q := by simp only [branch, Machine.withGuard, decide_eq_true_eq]

theorem machine_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (machine P a F h).selected q = true := by
  change (_ || true) = true
  exact Bool.or_true _

theorem model_inside (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) (hq : InScope P q) :
    (machine P a F h).model q = IntegralMixedValueRowModel.value P F q := by
  change (if decide (InScope P q) then _ else _) = _
  rw [ite_eq_left (decide_eq_true hq)]
  exact IntegralMixedValueRowDispatcher.machine_model P a F h q

theorem model_component (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) (hq : InScope P q) :
    (machine P a F h).model q = IntegralMixedValueRowModel.component P F (phase q) q :=
  (model_inside P a F h q hq).trans
    (IntegralMixedValueRowModel.value_phase P F (phase q) q hq.2.1 hq.2.2 hq.1.1 hq.1.2.1 rfl)

theorem model_outside (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) (hq : ¬InScope P q) :
    (machine P a F h).model q = [] := by
  change (if decide (InScope P q) then _ else []) = []
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hq)]

theorem canonical (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a F h).model q := by
  by_cases HQ : InScope P q
  · rw [model_inside P a F h q HQ]
    exact IntegralMixedValueRowModel.canonical P F q
  · rw [model_outside P a F h q HQ]
    exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
end LeanCanny.Algebra.IntegralMixedValueRowScopedBits
