/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedGramNativeMomentPower

/-! # Native finite-label guards for Gram determinant matrix stages -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramUpperBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open scoped Classical

noncomputable def selectedFinite (P : Parameters) (p : Phase) (size : List Bool → ℕ) (q : List Bool) : Bool :=
  decide (selected P p q = true ∧ get P .row q < size q ∧ get P .col q < size q)

theorem selectedFinite_FP (P : Parameters) (a : Access P) (p : Phase) (size : List Bool → ℕ) (hs : BinaryFn size) :
    (fun q => [selectedFinite P p size q]) ∈ FP :=
  ((FPPred.of_flag (selected_FP P a p)).and (((get_binary P a .row).lt hs).and ((get_binary P a .col).lt hs))).flag_mem_FP

theorem selectedFinite_iff (P : Parameters) (p : Phase) (size : List Bool → ℕ) (q : List Bool) :
    selectedFinite P p size q = true ↔
      (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 3 ∧ isPhase p q) ∧
        get P .row q < size q ∧ get P .col q < size q := by
  simp only [selectedFinite, decide_eq_true_eq, selected_iff]

end LeanCanny.Algebra.IntegralMixedGramUpperBits
