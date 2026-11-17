/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RootLabelScore

/-! # Robust squared-error tests for integer fingerprints -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open scoped BigOperators Classical

def fingerprintScore (A b : ℝ) (target : ℤ) : ℝ :=
  1 - 4 * ((A - (target : ℝ)) ^ 2 + (b - 1) ^ 2)

/-- An approximate integer fingerprint and an approximate sign can be tested
with a fixed gap. No primeness or uniqueness hypothesis is needed for soundness. -/
theorem fingerprintScore_margin (A b : ℝ) (actual target : ℤ) (sigma : SignType)
    (hA : |A - (actual : ℝ)| ≤ (1 : ℝ) / 16)
    (hb : |b - (sigma : ℝ)| ≤ (1 : ℝ) / 16) :
    ((1 : ℝ) / 2 ≤ fingerprintScore A b target ∨
      fingerprintScore A b target ≤ -(1 : ℝ) / 2) ∧
    (0 < fingerprintScore A b target ↔ actual = target ∧ sigma = 1) := by
  have hpos (ha : actual = target) (hs : sigma = 1) :
      (1 : ℝ) / 2 ≤ fingerprintScore A b target := by
    subst target
    subst sigma
    have hAsq := pow_le_pow_left₀ (abs_nonneg _) hA 2
    have hbsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
    simp only [sq_abs, SignType.coe_one] at hAsq hbsq
    dsimp only [fingerprintScore]
    nlinarith
  have hneg (hmatch : ¬(actual = target ∧ sigma = 1)) :
      fingerprintScore A b target ≤ -(1 : ℝ) / 2 := by
    by_cases ha : actual = target
    · have hs : sigma ≠ 1 := fun hs => hmatch ⟨ha, hs⟩
      have hgap := one_le_abs_sign_difference sigma 1 hs
      have htri := abs_sub_le (sigma : ℝ) b 1
      rw [abs_sub_comm (sigma : ℝ) b] at htri
      simp only [SignType.coe_one] at hgap
      have hdist : (15 : ℝ) / 16 ≤ |b - 1| := by linarith
      have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 15 / 16) hdist 2
      rw [sq_abs] at hsq
      have := sq_nonneg (A - (target : ℝ))
      dsimp only [fingerprintScore]
      nlinarith
    · have hgap : (1 : ℝ) ≤ |(actual : ℝ) - (target : ℝ)| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr ha)
      have htri := abs_sub_le (actual : ℝ) A (target : ℝ)
      rw [abs_sub_comm (actual : ℝ) A] at htri
      have hdist : (15 : ℝ) / 16 ≤ |A - (target : ℝ)| := by linarith
      have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 15 / 16) hdist 2
      rw [sq_abs] at hsq
      have := sq_nonneg (b - 1)
      dsimp only [fingerprintScore]
      nlinarith
  by_cases hm : actual = target ∧ sigma = 1
  · have hp := hpos hm.1 hm.2
    exact ⟨Or.inl hp, ⟨fun _ => hm, fun _ => by linarith⟩⟩
  · have hn := hneg hm
    exact ⟨Or.inr hn, ⟨fun hp => by linarith, fun he => (hm he).elim⟩⟩

/-- Summing bounded nonnegative integer weights preserves a sufficiently
accurate sign approximation. The denominator depends on the total weight. -/
theorem weighted_sign_error_le {m : ℕ} (w : Fin m → ℕ) (A : Fin m → ℝ)
    (sigma : Fin m → SignType) (M : ℕ) (hM : 1 ≤ M)
    (hweight : ∑ i, w i ≤ M)
    (hA : ∀ i, |A i - (sigma i : ℝ)| ≤ (16 * (M : ℝ))⁻¹) :
    |(∑ i, (w i : ℝ) * A i) - ((∑ i, (w i : ℤ) * (sigma i : ℤ) : ℤ) : ℝ)| ≤
      (1 : ℝ) / 16 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hwr : (∑ i, (w i : ℝ)) ≤ M := by exact_mod_cast hweight
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, SignType.intCast_cast]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(w i : ℝ) * A i - (w i : ℝ) * (sigma i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, (w i : ℝ) * |A i - (sigma i : ℝ)| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ i, (w i : ℝ) * (16 * (M : ℝ))⁻¹ :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hA i) (Nat.cast_nonneg _))
    _ = (∑ i, (w i : ℝ)) * (16 * (M : ℝ))⁻¹ := (Finset.sum_mul _ _ _).symm
    _ ≤ (M : ℝ) * (16 * (M : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right hwr (by positivity)
    _ = (1 : ℝ) / 16 := by field_simp

end LeanCanny.CountingHierarchy
