/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RationalSignProduct
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # One dyadic factor contracts the sign-product ratio -/

public section

namespace LeanCanny.CountingHierarchy

/-- The product contains a scale within a factor of two of every positive
 input in its advertised dyadic range. That factor contracts by `1/3`. -/
theorem exists_good_dyadic_sign_factor (B : ℕ) (z : ℝ)
    (hlo : ((2 : ℝ) ^ B)⁻¹ ≤ z) (hhi : z ≤ (2 : ℝ) ^ B) :
    ∃ j : ℕ, j < 2 * B + 1 ∧
      |(2 : ℝ) ^ (j - B) - (2 : ℝ) ^ (B - j) * z| ≤
        ((2 : ℝ) ^ (j - B) + (2 : ℝ) ^ (B - j) * z) / 3 := by
  have hpow : 0 < (2 : ℝ) ^ B := by positivity
  have htlo : 1 ≤ (2 : ℝ) ^ B * z := by
    have h := mul_le_mul_of_nonneg_left hlo hpow.le
    rw [mul_inv_cancel₀ hpow.ne'] at h
    exact h
  have hthi : (2 : ℝ) ^ B * z ≤ (2 : ℝ) ^ (2 * B) := by
    calc
      _ ≤ (2 : ℝ) ^ B * (2 : ℝ) ^ B := mul_le_mul_of_nonneg_left hhi hpow.le
      _ = _ := by rw [← pow_add]; congr 1; omega
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near htlo (by norm_num : (1 : ℝ) < 2)
  have hjB : j ≤ 2 * B := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hjlo.trans hthi)
  refine ⟨j, by omega, ?_⟩
  let w : ℝ := 2 ^ min B j
  have hw : 0 < w := by dsimp only [w]; positivity
  have ha : w * (2 : ℝ) ^ (j - B) = (2 : ℝ) ^ j := by
    dsimp only [w]
    rw [← pow_add]
    congr 1
    omega
  have hb : w * (2 : ℝ) ^ (B - j) = (2 : ℝ) ^ B := by
    dsimp only [w]
    rw [← pow_add]
    congr 1
    omega
  have hl : w * ((2 : ℝ) ^ (j - B) - (2 : ℝ) ^ (B - j) * z) =
      (2 : ℝ) ^ j - (2 : ℝ) ^ B * z := by rw [mul_sub, ← mul_assoc, ha, hb]
  have hr : w * ((2 : ℝ) ^ (j - B) + (2 : ℝ) ^ (B - j) * z) =
      (2 : ℝ) ^ j + (2 : ℝ) ^ B * z := by rw [mul_add, ← mul_assoc, ha, hb]
  have hs : |w * ((2 : ℝ) ^ (j - B) - (2 : ℝ) ^ (B - j) * z)| ≤
      w * (((2 : ℝ) ^ (j - B) + (2 : ℝ) ^ (B - j) * z) / 3) := by
    rw [← mul_div_assoc, hl, hr, abs_of_nonpos (by linarith)]
    rw [pow_succ] at hjhi
    linarith
  rw [abs_mul, abs_of_pos hw] at hs
  exact (mul_le_mul_iff_right₀ hw).mp hs

end LeanCanny.CountingHierarchy
