/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeOriginal
public import LeanCanny.Algebra.IntegralMixedVirtualCaps
/-! # Valid-prefix selectors for current-reply virtual branches -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def selectedValid (P : Parameters) (p : Phase) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q) && selected P p q

theorem selectedValid_FP (P : Parameters) (a : Access P) (p : Phase) : (fun q => [selectedValid P p q]) ∈ FP := by
  have HS := ((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 1)).and (isPhase_FP p)
  exact mem_FP_of_eq ((IntegralMixedVirtualCaps.valid_FP P a).and HS).flag_mem_FP
    (fun q => by
      by_cases hv : IntegralMixedVirtualCaps.valid P q <;>
        by_cases hr : IntegralMixedRoutineTaskBits.routine P q = 1 <;>
        by_cases hp : isPhase p q <;>
        simp [selectedValid, selected, IntegralMixedRoutineTaskBits.Routine.code, hv, hr, hp])

theorem selectedValid_iff (P : Parameters) (p : Phase) (q : List Bool) : selectedValid P p q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ (IntegralMixedRoutineTaskBits.routine P q = 1 ∧ isPhase p q) := by
  simp only [selectedValid, Bool.and_eq_true, decide_eq_true_eq, selected_iff]
end LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits
