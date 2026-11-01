/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullCriticalCanonical
/-! # The mixed critical dispatcher respects routine, context, and phase boundaries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullCriticalDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] physicalMachine virtualMachine

theorem model_none (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hp : ¬IntegralMixedRoutineContextGuard.Selected P 1 1 1 q)
    (hv : ¬IntegralMixedRoutineContextGuard.Selected P 1 2 4 q) : (machine P a D h).model q = [] := by
  change (if decide (IntegralMixedRoutineContextGuard.Selected P 1 1 1 q) then _ else
    if decide (IntegralMixedRoutineContextGuard.Selected P 1 2 4 q) then _ else []) = []
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hp), ite_eq_right (by simpa only [decide_eq_true_eq] using hv)]

theorem model_invalid (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hv : ¬IntegralMixedVirtualCaps.valid P q) : (machine P a D h).model q = [] :=
  model_none P a D h q (fun hc => hv hc.1) (fun hc => hv hc.1)

theorem model_other_routine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q ≠ 1) : (machine P a D h).model q = [] :=
  model_none P a D h q (fun hc => hr hc.2.1) (fun hc => hr hc.2.1)

theorem model_integer_context (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hx : get P .slot15 q = 0) : (machine P a D h).model q = [] := by
  apply model_none
  all_goals intro hc; have := hc.2.2.1; omega

theorem model_other_context (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hx : 4 < get P .slot15 q) : (machine P a D h).model q = [] := by
  apply model_none
  all_goals intro hc; have := hc.2.2.2; omega

theorem model_companion_phase (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hp : phase q = 26) : (machine P a D h).model q = [] := by
  have hP : (physicalMachine P a D h).model q = [] := by
    unfold physicalMachine
    exact IntegralMixedCriticalPhaseBoundary.physical P a _ h.physical h.physicalOriginal q hp
  have hV : (virtualMachine P a D h).model q = [] := by
    unfold virtualMachine
    exact IntegralMixedCriticalPhaseBoundary.virtual P a _ _ h.virtualOriginal q hp
  change (if decide (IntegralMixedRoutineContextGuard.Selected P 1 1 1 q) then (physicalMachine P a D h).model q else
    if decide (IntegralMixedRoutineContextGuard.Selected P 1 2 4 q) then (virtualMachine P a D h).model q else []) = []
  rw [hP, hV]
  split_ifs <;> rfl

end LeanCanny.Algebra.IntegralMixedFullCriticalDispatcherBits
