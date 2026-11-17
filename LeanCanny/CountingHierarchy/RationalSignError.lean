/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.DyadicSignFactor
public import Mathlib.Basic.Sign.Basic

/-! # Quantitative error of the rational sign approximation -/

public section

namespace LeanCanny.CountingHierarchy

open scoped BigOperators Classical

private theorem even_power_abs (x : ℝ) (s : ℕ) : x ^ (2 * s) = |x| ^ (2 * s) := by
  rw [← abs_pow, abs_of_nonneg]
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

private theorem prod_le_scaled_prod {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f g : ι → ℝ) (i : ι) (hi : i ∈ S) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hf : ∀ j ∈ S, 0 ≤ f j) (hg : ∀ j ∈ S, 0 ≤ g j)
    (hle : ∀ j ∈ S, f j ≤ g j) (hgood : f i ≤ ρ * g i) :
    (∏ j ∈ S, f j) ≤ ρ * ∏ j ∈ S, g j := by
  have he : (∏ j ∈ S.erase i, f j) ≤ ∏ j ∈ S.erase i, g j :=
    Finset.prod_le_prod₀ (fun j hj => hf j (Finset.mem_of_mem_erase hj))
      (fun j hj => hle j (Finset.mem_of_mem_erase hj))
  rw [← Finset.mul_prod_erase S f hi, ← Finset.mul_prod_erase S g hi]
  exact (mul_le_mul hgood he
    (Finset.prod_nonneg (fun j hj => hf j (Finset.mem_of_mem_erase hj)))
    (mul_nonneg hρ (hg i hi))).trans_eq (by ring)

/-- On the positive dyadic range, the reflected product is exponentially
 smaller than the positive product. -/
theorem signProductValue_reflection_le (B s : ℕ) (z : ℝ)
    (hlo : ((2 : ℝ) ^ B)⁻¹ ≤ z) (hhi : z ≤ (2 : ℝ) ^ B) :
    signProductValue B s (-z) ≤ ((3 : ℝ) ^ (2 * s))⁻¹ * signProductValue B s z := by
  have hz : 0 ≤ z := (inv_nonneg.mpr (by positivity)).trans hlo
  let a (j : ℕ) : ℝ := 2 ^ (j - B)
  let b (j : ℕ) : ℝ := 2 ^ (B - j)
  have habs (j : ℕ) : |a j - b j * z| ≤ a j + b j * z := by
    have ha : 0 ≤ a j := by dsimp only [a]; positivity
    have hb : 0 ≤ b j * z := mul_nonneg (by dsimp only [b]; positivity) hz
    rw [abs_le]
    constructor <;> linarith
  have hp (x : ℝ) : 0 ≤ x ^ (2 * s) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
  obtain ⟨i, hi, hgood⟩ := exists_good_dyadic_sign_factor B z hlo hhi
  have hpow : (a i - b i * z) ^ (2 * s) ≤
      ((3 : ℝ) ^ (2 * s))⁻¹ * (a i + b i * z) ^ (2 * s) := by
    rw [even_power_abs]
    have h := pow_le_pow_left₀ (abs_nonneg _) hgood (2 * s)
    rw [div_pow] at h
    simpa only [div_eq_mul_inv, mul_comm, a, b] using h
  rw [signProductValue_eq, signProductValue_eq]
  simp only [mul_neg, ← sub_eq_add_neg]
  exact prod_le_scaled_prod (Finset.range (2 * B + 1))
    (fun j => (a j - b j * z) ^ (2 * s)) (fun j => (a j + b j * z) ^ (2 * s))
    i (Finset.mem_range.mpr hi) _ (by positivity) (fun j _ => hp _)
    (fun j _ => hp _) (fun j _ => by
      rw [even_power_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (habs j) _) hpow

/-- The normalized difference approximates `+1` with the manuscript's
 uniform exponential error bound. -/
theorem rationalSignApproximation_error_pos (B s : ℕ) (z : ℝ)
    (hlo : ((2 : ℝ) ^ B)⁻¹ ≤ z) (hhi : z ≤ (2 : ℝ) ^ B) :
    |rationalSignApproximation B s z - 1| ≤ 2 * ((3 : ℝ) ^ (2 * s))⁻¹ := by
  have hz : 0 ≤ z := (inv_nonneg.mpr (by positivity)).trans hlo
  exact sign_difference_error_of_ratio _ _ _
    ((by norm_num : (0 : ℝ) < 1).trans_le (one_le_signProductValue B s z hz))
    (signProductValue_nonneg B s (-z)) (by positivity)
    (signProductValue_reflection_le B s z hlo hhi)

/-- The oddness identity gives the corresponding approximation to `-1`. -/
theorem rationalSignApproximation_error_neg (B s : ℕ) (z : ℝ)
    (hlo : ((2 : ℝ) ^ B)⁻¹ ≤ -z) (hhi : -z ≤ (2 : ℝ) ^ B) :
    |rationalSignApproximation B s z + 1| ≤ 2 * ((3 : ℝ) ^ (2 * s))⁻¹ := by
  have h := rationalSignApproximation_error_pos B s (-z) hlo hhi
  rw [rationalSignApproximation_neg] at h
  have he : rationalSignApproximation B s z + 1 =
      -(-rationalSignApproximation B s z - 1) := by ring
  rw [he, abs_neg]
  exact h

/-- The approximation handles zero exactly and approximates both nonzero
 signs on the full advertised dyadic range. -/
theorem rationalSignApproximation_error (B s : ℕ) (z : ℝ)
    (hz : z = 0 ∨ (((2 : ℝ) ^ B)⁻¹ ≤ |z| ∧ |z| ≤ (2 : ℝ) ^ B)) :
    |rationalSignApproximation B s z - (SignType.sign z : ℝ)| ≤
      2 * ((3 : ℝ) ^ (2 * s))⁻¹ := by
  by_cases hzero : z = 0
  · subst z
    rw [rationalSignApproximation_zero, sign_zero, SignType.coe_zero, sub_zero, abs_zero]
    positivity
  · obtain ⟨hlo, hhi⟩ := hz.resolve_left hzero
    rcases lt_or_gt_of_ne hzero with hn | hp
    · rw [sign_neg hn, SignType.coe_neg_one, sub_neg_eq_add]
      exact rationalSignApproximation_error_neg B s z
        (by simpa only [abs_of_neg hn] using hlo) (by simpa only [abs_of_neg hn] using hhi)
    · rw [sign_pos hp, SignType.coe_one]
      exact rationalSignApproximation_error_pos B s z
        (by simpa only [abs_of_pos hp] using hlo) (by simpa only [abs_of_pos hp] using hhi)

end LeanCanny.CountingHierarchy
