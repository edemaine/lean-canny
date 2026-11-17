/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RationalSignError

/-! # Choosing a short repetition exponent for sign margins -/

public section

namespace LeanCanny.CountingHierarchy

theorem sign_error_le_inverse_margin (M s : ℕ) (hM : 1 ≤ M) (hs : 16 * M ≤ s) :
    2 * ((3 : ℝ) ^ (2 * s))⁻¹ ≤ (16 * (M : ℝ))⁻¹ := by
  have hnat : 32 * M ≤ 3 ^ (2 * s) := by
    calc
      _ ≤ 2 * s := by omega
      _ ≤ 2 ^ (2 * s) := (Nat.lt_two_pow_self (n := 2 * s)).le
      _ ≤ _ := Nat.pow_le_pow_left (by decide) _
  have hreal : 32 * (M : ℝ) ≤ (3 : ℝ) ^ (2 * s) := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < 16 * M := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    positivity
  rw [← div_eq_mul_inv, ← one_div (16 * (M : ℝ))]
  apply (div_le_div_iff₀ (pow_pos (by norm_num) _) hpos).mpr
  nlinarith

/-- Repetition `s=16M` yields the uniform error used by root-label scores. -/
theorem rationalSignApproximation_margin (B M : ℕ) (hM : 1 ≤ M) (z : ℝ)
    (hz : z = 0 ∨ (((2 : ℝ) ^ B)⁻¹ ≤ |z| ∧ |z| ≤ (2 : ℝ) ^ B)) :
    |rationalSignApproximation B (16 * M) z - (SignType.sign z : ℝ)| ≤ (16 * (M : ℝ))⁻¹ :=
  (rationalSignApproximation_error B (16 * M) z hz).trans
    (sign_error_le_inverse_margin M (16 * M) hM le_rfl)

theorem one_le_abs_sign_difference (a b : SignType) (hab : a ≠ b) :
    (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
  cases a <;> cases b <;> norm_num at *

end LeanCanny.CountingHierarchy
