/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ClearedSignTests

/-! # An integer polynomial recognizing a finite list of sign conditions -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial
open scoped BigOperators Classical

/-- Positive-denominator clearing of the squared-error score. All operations
 are integer additions, multiplications, powers and indexed products. -/
@[expose] noncomputable def rootLabelPolynomial {m : ℕ}
    (B s : ℕ) (g : Fin m → Polynomial ℤ) (t : Fin m → SignType) : Polynomial ℤ :=
  (signTestCommonDenominator B s g) ^ 2 - Polynomial.C (4 : ℤ) *
    ∑ i, (signTestClearedNumerator B s g i - Polynomial.C (t i : ℤ) *
      signTestCommonDenominator B s g) ^ 2

theorem rootLabelPolynomial_eval {m : ℕ} (B s : ℕ)
    (g : Fin m → Polynomial ℤ) (t : Fin m → SignType) (x : ℝ) :
    (rootLabelPolynomial B s g t).eval₂ (Int.castRingHom ℝ) x =
      ((signTestCommonDenominator B s g).eval₂ (Int.castRingHom ℝ) x) ^ 2 *
        rootLabelScore (fun i => rationalSignApproximation B s ((g i).eval₂ (Int.castRingHom ℝ) x)) t := by
  let E := (signTestCommonDenominator B s g).eval₂ (Int.castRingHom ℝ) x
  let A (i : Fin m) := rationalSignApproximation B s ((g i).eval₂ (Int.castRingHom ℝ) x)
  rw [rootLabelPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Int.coe_castRingHom, Int.cast_ofNat, SignType.intCast_cast, signTestClearedNumerator_eval]
  change E ^ 2 - 4 * (∑ i, (E * A i - (t i : ℝ) * E) ^ 2) = E ^ 2 * rootLabelScore A t
  have hs : (∑ i, (E * A i - (t i : ℝ) * E) ^ 2) = E ^ 2 * ∑ i, (A i - (t i : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs, rootLabelScore]
  ring

/-- Wherever the test values are zero or bounded away from zero by the
 advertised dyadic bound, the integer label has a uniform sign margin and
 is positive exactly when all target signs hold. -/
theorem rootLabelPolynomial_margin {m : ℕ} (hm : 1 ≤ m) (B : ℕ)
    (g : Fin m → Polynomial ℤ) (t : Fin m → SignType) (x : ℝ)
    (hvalues : ∀ i, (g i).eval₂ (Int.castRingHom ℝ) x = 0 ∨
      (((2 : ℝ) ^ B)⁻¹ ≤ |(g i).eval₂ (Int.castRingHom ℝ) x| ∧
        |(g i).eval₂ (Int.castRingHom ℝ) x| ≤ (2 : ℝ) ^ B)) :
    ((1 : ℝ) / 2 ≤ (rootLabelPolynomial B (16 * m) g t).eval₂ (Int.castRingHom ℝ) x ∨
      (rootLabelPolynomial B (16 * m) g t).eval₂ (Int.castRingHom ℝ) x ≤ -(1 : ℝ) / 2) ∧
      (0 < (rootLabelPolynomial B (16 * m) g t).eval₂ (Int.castRingHom ℝ) x ↔
        ∀ i, SignType.sign ((g i).eval₂ (Int.castRingHom ℝ) x) = t i) := by
  rw [rootLabelPolynomial_eval]
  exact cleared_rootLabelScore_margin hm _ _ t
    (fun i => rationalSignApproximation_margin B m hm _ (hvalues i)) _
    (signTestCommonDenominator_eval_ge_one B (16 * m) g x)

end LeanCanny.CountingHierarchy
