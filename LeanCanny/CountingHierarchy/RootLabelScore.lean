/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RationalSignMargin

/-! # Squared-error scores for a short list of sign tests -/

public section

namespace LeanCanny.CountingHierarchy

open scoped BigOperators Classical

@[expose] noncomputable def rootLabelScore {m : ℕ} (A : Fin m → ℝ) (t : Fin m → SignType) : ℝ :=
  1 - 4 * ∑ i, (A i - (t i : ℝ)) ^ 2

private theorem inverse_test_margin_le {m : ℕ} (hm : 1 ≤ m) :
    (16 * (m : ℝ))⁻¹ ≤ (1 : ℝ) / 16 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 16)
    (show (16 : ℝ) ≤ 16 * m by nlinarith)

/-- Agreement of all true signs with the target signs gives a positive
 score with margin `1/2`, even though the tests are only approximated. -/
theorem rootLabelScore_match {m : ℕ} (hm : 1 ≤ m) (A : Fin m → ℝ) (σ t : Fin m → SignType)
    (hA : ∀ i, |A i - (σ i : ℝ)| ≤ (16 * (m : ℝ))⁻¹)
    (hmatch : ∀ i, σ i = t i) : (1 : ℝ) / 2 ≤ rootLabelScore A t := by
  let δ : ℝ := (16 * (m : ℝ))⁻¹
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδle : δ ≤ (1 : ℝ) / 16 := inverse_test_margin_le hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcancel : (m : ℝ) * δ = (1 : ℝ) / 16 := by
    dsimp only [δ]
    field_simp
  have hsum : (∑ i, (A i - (t i : ℝ)) ^ 2) ≤ (1 : ℝ) / 256 := by
    calc
      _ ≤ ∑ _i : Fin m, δ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := pow_le_pow_left₀ (abs_nonneg _) (hA i) 2
        simpa only [hmatch i, sq_abs] using hi
      _ = (m : ℝ) * δ ^ 2 := by simp
      _ = ((m : ℝ) * δ) * δ := by ring
      _ ≤ ((1 : ℝ) / 16) * ((1 : ℝ) / 16) := by
        rw [hcancel]
        exact mul_le_mul_of_nonneg_left hδle (by norm_num)
      _ = (1 : ℝ) / 256 := by norm_num
  dsimp only [rootLabelScore]
  linarith

/-- A single sign mismatch gives a negative score with margin `1/2`. -/
theorem rootLabelScore_mismatch {m : ℕ} (hm : 1 ≤ m) (A : Fin m → ℝ) (σ t : Fin m → SignType)
    (hA : ∀ i, |A i - (σ i : ℝ)| ≤ (16 * (m : ℝ))⁻¹)
    (hmatch : ¬∀ i, σ i = t i) : rootLabelScore A t ≤ -(1 : ℝ) / 2 := by
  obtain ⟨i, hi⟩ := not_forall.mp hmatch
  have hδle := inverse_test_margin_le hm
  have hgap := one_le_abs_sign_difference (σ i) (t i) hi
  have htri := abs_sub_le (σ i : ℝ) (A i) (t i : ℝ)
  rw [abs_sub_comm (σ i : ℝ) (A i)] at htri
  have hdist : (15 : ℝ) / 16 ≤ |A i - (t i : ℝ)| := by
    have he := hA i
    linarith
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 15 / 16) hdist 2
  rw [sq_abs] at hsq
  have hsum : (A i - (t i : ℝ)) ^ 2 ≤ ∑ j, (A j - (t j : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin m => (A j - (t j : ℝ)) ^ 2)
      (fun j _ => sq_nonneg (A j - (t j : ℝ))) (Finset.mem_univ i)
  dsimp only [rootLabelScore]
  nlinarith

/-- Clearing denominators with a factor at least one preserves the strict
 score dichotomy and the acceptance condition. -/
theorem cleared_rootLabelScore_margin {m : ℕ} (hm : 1 ≤ m)
    (A : Fin m → ℝ) (σ t : Fin m → SignType)
    (hA : ∀ i, |A i - (σ i : ℝ)| ≤ (16 * (m : ℝ))⁻¹) (E : ℝ) (hE : 1 ≤ E) :
    ((1 : ℝ) / 2 ≤ E ^ 2 * rootLabelScore A t ∨
      E ^ 2 * rootLabelScore A t ≤ -(1 : ℝ) / 2) ∧
      (0 < E ^ 2 * rootLabelScore A t ↔ ∀ i, σ i = t i) := by
  have hE2 : 1 ≤ E ^ 2 := by nlinarith
  by_cases hmatch : ∀ i, σ i = t i
  · have hs := rootLabelScore_match hm A σ t hA hmatch
    have hpos : (1 : ℝ) / 2 ≤ E ^ 2 * rootLabelScore A t := by nlinarith
    exact ⟨Or.inl hpos, ⟨fun _ => hmatch, fun _ => by linarith⟩⟩
  · have hs := rootLabelScore_mismatch hm A σ t hA hmatch
    have hneg : E ^ 2 * rootLabelScore A t ≤ -(1 : ℝ) / 2 := by nlinarith
    exact ⟨Or.inr hneg, ⟨fun hh => by linarith, fun hh => (hmatch hh).elim⟩⟩

end LeanCanny.CountingHierarchy
