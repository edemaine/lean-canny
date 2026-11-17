/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientMass
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The integer product used to approximate real signs -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial
open scoped BigOperators Classical

/-- The index `j` represents the signed dyadic exponent `j-B`, avoiding
 signed exponents in the integer polynomial itself. -/
@[expose] noncomputable def rationalSignProduct (B s : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Finset.range (2 * B + 1),
    (Polynomial.C ((2 : ℤ) ^ (j - B)) + Polynomial.C ((2 : ℤ) ^ (B - j)) * Polynomial.X) ^ (2 * s)

@[expose] noncomputable def signProductValue (B s : ℕ) (z : ℝ) : ℝ :=
  (rationalSignProduct B s).eval₂ (Int.castRingHom ℝ) z

@[expose] noncomputable def rationalSignApproximation (B s : ℕ) (z : ℝ) : ℝ :=
  (signProductValue B s z - signProductValue B s (-z)) /
    (signProductValue B s z + signProductValue B s (-z))

theorem signProductValue_eq (B s : ℕ) (z : ℝ) :
    signProductValue B s z = ∏ j ∈ Finset.range (2 * B + 1),
      ((2 : ℝ) ^ (j - B) + (2 : ℝ) ^ (B - j) * z) ^ (2 * s) := by
  simp only [signProductValue, rationalSignProduct, Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat]

theorem signProductValue_nonneg (B s : ℕ) (z : ℝ) : 0 ≤ signProductValue B s z := by
  rw [signProductValue_eq]
  apply Finset.prod_nonneg
  intro j _
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) s

theorem one_le_signProductValue (B s : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    1 ≤ signProductValue B s z := by
  rw [signProductValue_eq]
  apply Finset.one_le_prod₀
  intro j _
  apply one_le_pow₀
  have ha : (1 : ℝ) ≤ 2 ^ (j - B) := one_le_pow₀ (by norm_num)
  have hb : (0 : ℝ) ≤ 2 ^ (B - j) * z := mul_nonneg (by positivity) hz
  linarith

/-- Positive denominators can be cleared uniformly, including at zero. -/
theorem signProduct_denominator_ge_one (B s : ℕ) (z : ℝ) :
    1 ≤ signProductValue B s z + signProductValue B s (-z) := by
  by_cases hz : 0 ≤ z
  · exact (one_le_signProductValue B s z hz).trans
      (le_add_of_nonneg_right (signProductValue_nonneg B s (-z)))
  · have hn : 0 ≤ -z := by linarith
    exact (one_le_signProductValue B s (-z) hn).trans
      (le_add_of_nonneg_left (signProductValue_nonneg B s z))

theorem rationalSignApproximation_zero (B s : ℕ) : rationalSignApproximation B s 0 = 0 := by
  simp only [rationalSignApproximation, neg_zero, sub_self, zero_div]

theorem rationalSignApproximation_neg (B s : ℕ) (z : ℝ) :
    rationalSignApproximation B s (-z) = -rationalSignApproximation B s z := by
  simp only [rationalSignApproximation, neg_neg]
  rw [add_comm (signProductValue B s (-z)) (signProductValue B s z)]
  ring

/-- A ratio bound on the two nonnegative products gives an error bound
 for their normalized signed difference. -/
theorem sign_difference_error_of_ratio (A C ε : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (hCA : C ≤ ε * A) :
    |(A - C) / (A + C) - 1| ≤ 2 * ε := by
  have hden : 0 < A + C := by linarith
  have hle : (A - C) / (A + C) ≤ 1 := (div_le_iff₀ hden).mpr (by linarith)
  rw [abs_of_nonpos (by linarith)]
  have he : -((A - C) / (A + C) - 1) = 2 * C / (A + C) := by
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ hden).mpr
  have := mul_nonneg hε hC
  nlinarith

end LeanCanny.CountingHierarchy
