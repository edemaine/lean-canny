/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramContextPatch
public import LeanCanny.Algebra.IntegralMixedRoutineContextGuard
/-! # Native Gram arithmetic restricted to virtual creating contexts -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramScopedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedGramUpperDispatcher.machine

def InScope (P : Parameters) (q : List Bool) : Prop := IntegralMixedRoutineContextGuard.Selected P 3 2 4 q ∧ PhaseAllowed q

theorem phase_allowed_FP : FPPred PhaseAllowed :=
  ((BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27)).eq (BinaryFn.const 19)).or
    (((BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27)).eq (BinaryFn.const 21)).or
      (((BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27)).eq (BinaryFn.const 22)).or
        (((BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27)).eq (BinaryFn.const 23)).or
          ((BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27)).eq (BinaryFn.const 24)))))
theorem selected_FP (P : Parameters) (a : Access P) : FPPred (InScope P) :=
  (IntegralMixedRoutineContextGuard.selected_FP P a 3 2 4).and phase_allowed_FP

noncomputable def branch (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  (IntegralMixedGramUpperDispatcher.machine P a F h).withGuard (fun q => decide (InScope P q)) (selected_FP P a).flag_mem_FP
noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine := (branch P a F h).choose zero

theorem branch_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q)) (hr : Rows P F (fun q => residueBits (x q))) (hm : Matches P F (fun q => residueBits (x q))) :
    Correct (branch P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  let y := patch P F x
  have HM := patch_matches P F x hm
  have HR := patch_rows P F x hr
  have HY := IntegralMixedGramUpperDispatcher.correct P a F h g y HR HM
  apply withGuard_oracle_correct _ _ _ (fun q => residueBits (y q)) (fun q => residueBits (x q)) _ HY
  · intro q _
    exact IntegralMixedGramUpperDispatcher.machine_selected P a F h q
  · intro q hq budget c hreq
    have HQ : InScope P q := of_decide_eq_true hq
    have HE := IntegralMixedGramContextBits.requests_context P a F h g (fun q => residueBits (y q)) HM
      q (IntegralMixedGramUpperDispatcher.machine_selected P a F h q) budget c hreq
    have HX : IntegralMixedVirtualContextBits.context P c := by
      unfold IntegralMixedVirtualContextBits.context
      rw [show get P .slot15 c = get P .slot15 q from HE]
      exact HQ.1.2.2
    exact congrArg residueBits (patch_good P F x c HX)

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q)) (hr : Rows P F (fun q => residueBits (x q))) (hm : Matches P F (fun q => residueBits (x q))) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  choose_correct _ _ _ _ (branch_correct P a F h g x hr hm) (zero_correct _ _)

theorem branch_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (branch P a F h).selected q = true ↔ InScope P q := by simp only [branch, Machine.withGuard, decide_eq_true_eq]

theorem model_inside (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) (hq : InScope P q) :
    (machine P a F h).model q = IntegralMixedGramUpperModel.value P F q := by
  change (if decide (InScope P q) then _ else _) = _
  rw [ite_eq_left (decide_eq_true hq)]
  exact IntegralMixedGramUpperDispatcher.machine_model P a F h q

theorem model_component (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) (hq : InScope P q) :
    (machine P a F h).model q = IntegralMixedGramUpperModel.component P F (phase q) q :=
  (model_inside P a F h q hq).trans (IntegralMixedGramUpperModel.value_phase P F q (phase q) hq.2 hq.1.1 hq.1.2.1 rfl)

theorem model_outside (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) (hq : ¬InScope P q) :
    (machine P a F h).model q = [] := by
  change (if decide (InScope P q) then _ else []) = []
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hq)]

theorem canonical (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a F h).model q := by
  by_cases HQ : InScope P q
  · rw [model_inside P a F h q HQ]
    exact IntegralMixedGramUpperModel.canonical P F q
  · rw [model_outside P a F h q HQ]
    exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
end LeanCanny.Algebra.IntegralMixedGramScopedBits
