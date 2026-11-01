/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullAlgebraCurrent
/-! # Canonical current values of the joint critical and producer dispatcher -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullAlgebraDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    if decide (IntegralMixedRoutineTaskBits.routine P q = 1) then
      (IntegralMixedFullCriticalDispatcherBits.machine P a D h.critical).model q else
      if decide (IntegralMixedRoutineTaskBits.routine P q = 6) then
        (IntegralMixedFullProducerDispatcherBits.machine P a D h.producer).model q else []
  split_ifs
  · exact IntegralMixedFullCriticalDispatcherBits.canonical P a D h.critical q
  · exact IntegralMixedFullProducerDispatcherBits.canonical P a D h.producer q
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

theorem model_other_routine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (h1 : IntegralMixedRoutineTaskBits.routine P q ≠ 1) (h6 : IntegralMixedRoutineTaskBits.routine P q ≠ 6) :
    (machine P a D h).model q = [] := by
  change (if decide (IntegralMixedRoutineTaskBits.routine P q = 1) then _ else
    if decide (IntegralMixedRoutineTaskBits.routine P q = 6) then _ else []) = []
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using h1), ite_eq_right (by simpa only [decide_eq_true_eq] using h6)]

end LeanCanny.Algebra.IntegralMixedFullAlgebraDispatcherBits
