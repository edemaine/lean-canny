/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullDeterminant
public import LeanCanny.Algebra.IntegralMixedRawDispatcherCurrent
/-! # One native controller for every mixed-history arithmetic routine -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable abbrev family := IntegralMixedFullEntryBits.family

structure Controls (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) where
  arithmetic : IntegralMixedArithmeticEntriesBits.Controls P D
  kind : IntegralMixedRawKindBits.Metadata (family P D)
noncomputable abbrev input (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedFullEntryBits.input P a D h.arithmetic.core
noncomputable def raw (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedRawDispatcherBits.machine P a (family P D) (input P a D h) h.kind h.arithmetic.core.scalar.full.degree
noncomputable def rawBranch (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  (raw P a D h).withGuard (fun q => decide (IntegralMixedRoutineTaskBits.routine P q = 4))
    ((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 4)).flag_mem_FP
noncomputable def determinantBranch (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  (IntegralMixedFullDeterminantBits.machine P a D h.arithmetic.core).withGuard
    (fun q => decide (IntegralMixedRoutineTaskBits.routine P q = 3))
    ((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 3)).flag_mem_FP
noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  (rawBranch P a D h).choose ((determinantBranch P a D h).choose (IntegralMixedArithmeticEntriesBits.machine P a D h.arithmetic))

theorem model_raw (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 4) :
    (machine P a D h).model q = (raw P a D h).model q := by
  change (if decide (IntegralMixedRoutineTaskBits.routine P q = 4) then _ else _) = _
  rw [ite_eq_left (decide_eq_true hr)]
  rfl

theorem model_determinant (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 3) :
    (machine P a D h).model q = (IntegralMixedFullDeterminantBits.machine P a D h.arithmetic.core).model q := by
  have H4 : IntegralMixedRoutineTaskBits.routine P q ≠ 4 := by omega
  change (if decide (IntegralMixedRoutineTaskBits.routine P q = 4) then _ else
    if decide (IntegralMixedRoutineTaskBits.routine P q = 3) then _ else _) = _
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using H4), ite_eq_left (decide_eq_true hr)]
  rfl

theorem model_arithmetic (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (h3 : IntegralMixedRoutineTaskBits.routine P q ≠ 3) (h4 : IntegralMixedRoutineTaskBits.routine P q ≠ 4) :
    (machine P a D h).model q = (IntegralMixedArithmeticEntriesBits.machine P a D h.arithmetic).model q := by
  change (if decide (IntegralMixedRoutineTaskBits.routine P q = 4) then _ else
    if decide (IntegralMixedRoutineTaskBits.routine P q = 3) then _ else _) = _
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using h4), ite_eq_right (by simpa only [decide_eq_true_eq] using h3)]

theorem selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    (machine P a D h).selected q = true := by
  change (_ || (_ || (IntegralMixedArithmeticEntriesBits.machine P a D h.arithmetic).selected q)) = true
  rw [IntegralMixedArithmeticEntriesBits.selected, Bool.or_true, Bool.or_true]

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h).model q := by
  by_cases h4 : IntegralMixedRoutineTaskBits.routine P q = 4
  · rw [model_raw P a D h q h4]
    exact IntegralMixedRawDispatcherBits.canonical P a _ _ _ _ q
  · by_cases h3 : IntegralMixedRoutineTaskBits.routine P q = 3
    · rw [model_determinant P a D h q h3]
      exact IntegralMixedFullDeterminantBits.canonical P a D h.arithmetic.core q
    · rw [model_arithmetic P a D h q h3 h4]
      exact IntegralMixedArithmeticEntriesBits.canonical P a D h.arithmetic q

end LeanCanny.Algebra.IntegralMixedFullNativeBits
