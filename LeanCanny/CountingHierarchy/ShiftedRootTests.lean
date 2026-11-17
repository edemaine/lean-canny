/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.Separation
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.Linarith

/-! # Bounded shifts avoid zero test values while preserving sign margins -/

public section

namespace LeanCanny.CountingHierarchy

open scoped Classical

/-- Among `D+1` short integer shifts, one avoids zeros at all of at most
 `D` test points, including nonreal points. -/
theorem exists_bounded_shift_ne_zero (S : Finset ℂ) (D : ℕ) (hS : S.card ≤ D)
    (b : ℂ → ℂ) : ∃ e : ℕ, e ≤ D ∧ ∀ z ∈ S, b z + (e : ℂ) ≠ 0 := by
  let bad := S.image (fun z => -b z)
  obtain ⟨e, he, hnot⟩ := LeanCanny.Algebra.exists_nat_le_card_notMem bad
  refine ⟨e, he.trans (Finset.card_image_le.trans hS), ?_⟩
  intro z hz heq
  apply hnot
  have hcast : (e : ℂ) = -b z := by
    exact eq_neg_of_add_eq_zero_right heq
  rw [hcast]
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

/-- A positive label with margin `1/2` yields a strictly negative factor
 for every allowed shift. -/
theorem shifted_factor_neg (D e : ℕ) (hD : 1 ≤ D) (he : e ≤ D) (L : ℝ)
    (hL : (1 : ℝ) / 2 ≤ L) : -4 * (D : ℝ) * L + e ≤ -(D : ℝ) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have he' : (e : ℝ) ≤ D := by exact_mod_cast he
  nlinarith

/-- A negative label with margin `1/2` yields a strictly positive factor. -/
theorem shifted_factor_pos (D e : ℕ) (L : ℝ) (hL : L ≤ -(1 : ℝ) / 2) :
    2 * (D : ℝ) ≤ -4 * (D : ℝ) * L + e := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  nlinarith

/-- The dichotomy of label margins makes the shifted factor negative
 exactly where the label is positive. -/
theorem shifted_factor_neg_iff (D e : ℕ) (hD : 1 ≤ D) (he : e ≤ D) (L : ℝ)
    (hL : (1 : ℝ) / 2 ≤ L ∨ L ≤ -(1 : ℝ) / 2) :
    -4 * (D : ℝ) * L + e < 0 ↔ 0 < L := by
  rcases hL with hL | hL
  · have h := shifted_factor_neg D e hD he L hL
    have hD' : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    constructor <;> intro _ <;> linarith
  · have h := shifted_factor_pos D e L hL
    have hD' : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    constructor <;> intro hh <;> linarith

end LeanCanny.CountingHierarchy
