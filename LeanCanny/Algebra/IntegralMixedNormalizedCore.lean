/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullCoreScoped
public import LeanCanny.Algebra.IntegralMixedNormalizationScopedCurrent
/-! # Scalar, critical, normalization, and producer routines over one actual history -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedCoreBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Controls (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) where
  core : IntegralMixedFullCoreBits.Controls P D
  height : List Bool → ℕ
  height_binary : BinaryFn height
  height_bound : ∀ q, IntegralMixedVirtualCaps.valid P q → ∀ i j,
    (IntegralMixedNormalizationTopBits.top (IntegralMixedFullHistoryFamilyBits.family P D)
      (IntegralMixedVirtualTaskBits.saved P q) i j).natAbs ≤ 2 ^ height (RankedHistoryTask.root q)
  modulus_bound : ∀ r, 2 * IntegralMixedNormalizationTopBits.characteristicBudget P height r + 4 ≤ P.modulusBound r

noncomputable def normalization (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedNormalizationScopedBits.machine P a (IntegralMixedFullHistoryFamilyBits.family P D)
    (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.core.scalar.full) h.core.scalar.full.degree h.height h.height_binary

noncomputable def branch (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  (normalization P a D h).withGuard (fun q => decide (IntegralMixedRoutineTaskBits.routine P q = 5))
    ((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 5)).flag_mem_FP

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  (branch P a D h).choose (IntegralMixedFullCoreBits.machine P a D h.core)

theorem model_normalization (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 5) :
    (machine P a D h).model q = (normalization P a D h).model q := by
  change (if decide (IntegralMixedRoutineTaskBits.routine P q = 5) then _ else _) = _
  rw [ite_eq_left (decide_eq_true hr)]
  rfl

theorem model_core (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q ≠ 5) :
    (machine P a D h).model q = (IntegralMixedFullCoreBits.machine P a D h.core).model q := by
  change (if decide (IntegralMixedRoutineTaskBits.routine P q = 5) then _ else _) = _
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hr)]

theorem selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    (machine P a D h).selected q = true := by
  change (_ || (IntegralMixedFullCoreBits.machine P a D h.core).selected q) = true
  rw [IntegralMixedFullCoreBits.selected, Bool.or_true]

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h).model q := by
  by_cases hr : IntegralMixedRoutineTaskBits.routine P q = 5
  · rw [model_normalization P a D h q hr]
    exact IntegralMixedNormalizationScopedBits.canonical P a _ _ _ _ _ q
  · rw [model_core P a D h q hr]
    exact IntegralMixedFullCoreBits.canonical P a D h.core q

end LeanCanny.Algebra.IntegralMixedNormalizedCoreBits
