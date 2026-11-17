/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FingerprintLabelScore
public import LeanCanny.CountingHierarchy.ClearedSignTests

/-! # Integer polynomials testing a compressed derivative-sign fingerprint -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial
open scoped BigOperators Classical

noncomputable def fingerprintLabelPolynomial {m : ℕ} (B s : ℕ)
    (g : Fin (m + 1) → Polynomial ℤ) (w : Fin m → ℕ) (target : ℤ) : Polynomial ℤ :=
  let E := signTestCommonDenominator B s g
  let T := signTestClearedNumerator B s g
  E ^ 2 - C 4 * ((∑ i, C (w i : ℤ) * T i.succ) - C target * E) ^ 2 -
    C 4 * (T 0 - E) ^ 2

theorem fingerprintLabelPolynomial_eval {m : ℕ} (B s : ℕ)
    (g : Fin (m + 1) → Polynomial ℤ) (w : Fin m → ℕ) (target : ℤ) (x : ℝ) :
    (fingerprintLabelPolynomial B s g w target).eval₂ (Int.castRingHom ℝ) x =
      ((signTestCommonDenominator B s g).eval₂ (Int.castRingHom ℝ) x) ^ 2 *
        fingerprintScore (∑ i, (w i : ℝ) * rationalSignApproximation B s
          ((g i.succ).eval₂ (Int.castRingHom ℝ) x))
          (rationalSignApproximation B s ((g 0).eval₂ (Int.castRingHom ℝ) x)) target := by
  let E := (signTestCommonDenominator B s g).eval₂ (Int.castRingHom ℝ) x
  let A (i : Fin (m + 1)) := rationalSignApproximation B s ((g i).eval₂ (Int.castRingHom ℝ) x)
  rw [fingerprintLabelPolynomial]
  simp only [eval₂_sub, eval₂_pow, eval₂_mul, eval₂_C, eval₂_finsetSum,
    Int.coe_castRingHom, Int.cast_ofNat, Int.cast_natCast, signTestClearedNumerator_eval]
  change E ^ 2 - 4 * ((∑ i, (w i : ℝ) * (E * A i.succ)) - (target : ℝ) * E) ^ 2 -
    4 * (E * A 0 - E) ^ 2 = E ^ 2 * fingerprintScore (∑ i, (w i : ℝ) * A i.succ) (A 0) target
  have he : (∑ i, (w i : ℝ) * (E * A i.succ)) = E * ∑ i, (w i : ℝ) * A i.succ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, fingerprintScore]
  ring

/-- Denominator clearing preserves the score margin for every integer target,
including labels that do not isolate any root. -/
theorem fingerprintLabelPolynomial_margin {m : ℕ} (B M : ℕ)
    (g : Fin (m + 1) → Polynomial ℤ) (w : Fin m → ℕ) (target : ℤ) (x : ℝ)
    (hM : 1 ≤ M) (hw : ∑ i, w i ≤ M)
    (hvalues : ∀ i, (g i).eval₂ (Int.castRingHom ℝ) x = 0 ∨
      (((2 : ℝ) ^ B)⁻¹ ≤ |(g i).eval₂ (Int.castRingHom ℝ) x| ∧
        |(g i).eval₂ (Int.castRingHom ℝ) x| ≤ (2 : ℝ) ^ B)) :
    ((1 : ℝ) / 2 ≤ (fingerprintLabelPolynomial B (16 * M) g w target).eval₂ (Int.castRingHom ℝ) x ∨
      (fingerprintLabelPolynomial B (16 * M) g w target).eval₂ (Int.castRingHom ℝ) x ≤ -(1 : ℝ) / 2) ∧
    (0 < (fingerprintLabelPolynomial B (16 * M) g w target).eval₂ (Int.castRingHom ℝ) x ↔
      (∑ i, (w i : ℤ) * (SignType.sign ((g i.succ).eval₂ (Int.castRingHom ℝ) x) : ℤ)) = target ∧
      0 < (g 0).eval₂ (Int.castRingHom ℝ) x) := by
  let A (i : Fin (m + 1)) := rationalSignApproximation B (16 * M) ((g i).eval₂ (Int.castRingHom ℝ) x)
  let sigma (i : Fin (m + 1)) := SignType.sign ((g i).eval₂ (Int.castRingHom ℝ) x)
  have hA (i) : |A i - (sigma i : ℝ)| ≤ (16 * (M : ℝ))⁻¹ :=
    rationalSignApproximation_margin B M hM _ (hvalues i)
  have herr := weighted_sign_error_le w (fun i => A i.succ) (fun i => sigma i.succ) M hM hw (fun i => hA i.succ)
  have hinv : (16 * (M : ℝ))⁻¹ ≤ (1 : ℝ) / 16 := by
    have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 16)
      (show (16 : ℝ) ≤ 16 * M by nlinarith)
  have h := fingerprintScore_margin _ _ _ target (sigma 0) herr ((hA 0).trans hinv)
  let E := (signTestCommonDenominator B (16 * M) g).eval₂ (Int.castRingHom ℝ) x
  have hE : 1 ≤ E := signTestCommonDenominator_eval_ge_one B (16 * M) g x
  have hE2 : 1 ≤ E ^ 2 := by nlinarith
  rw [fingerprintLabelPolynomial_eval]
  change ((1 : ℝ) / 2 ≤ E ^ 2 * fingerprintScore _ _ target ∨
    E ^ 2 * fingerprintScore _ _ target ≤ -(1 : ℝ) / 2) ∧ _
  constructor
  · rcases h.1 with hp | hn
    · left; nlinarith
    · right; nlinarith
  · have hepos : 0 < E ^ 2 := by nlinarith
    rw [mul_pos_iff_of_pos_left hepos, h.2]
    simp only [sigma, sign_eq_one_iff]

end LeanCanny.CountingHierarchy
