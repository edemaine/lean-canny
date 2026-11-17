/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Partial derivative values as coefficients of one translated polynomial

First and mixed second derivatives require only one coefficient extraction.
Repeated-coordinate second derivatives carry the explicit factor two.
-/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped Classical BigOperators

variable {ι R : Type*} [CommRing R]

@[expose] noncomputable def polynomialTranslation (z : ι → R) :
    MvPolynomial ι R →+* MvPolynomial ι R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (z i))

@[simp] theorem polynomialTranslation_C (z : ι → R) (r : R) :
    polynomialTranslation z (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [polynomialTranslation]

@[simp] theorem polynomialTranslation_X (z : ι → R) (i : ι) :
    polynomialTranslation z (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C (z i) := by
  simp [polynomialTranslation]

theorem eval_polynomialTranslation (z y : ι → R) (F : MvPolynomial ι R) :
    eval y (polynomialTranslation z F) = eval (fun i => y i + z i) F := by
  induction F using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem polynomialTranslation_pderiv (z : ι → R) (F : MvPolynomial ι R) (i : ι) :
    polynomialTranslation z (pderiv i F) = pderiv i (polynomialTranslation z F) := by
  induction F using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    by_cases hij : i = j
    · subst j
      simp [pderiv_X, hp]
    · simp [pderiv_X, hij, hp]

theorem constantCoeff_polynomialTranslation (z : ι → R) (F : MvPolynomial ι R) :
    (polynomialTranslation z F).coeff 0 = eval z F := by
  have h := eval_polynomialTranslation z (fun _ => 0) F
  simpa only [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq, zero_add] using h

theorem first_derivative_translation_coeff (z : ι → R) (F : MvPolynomial ι R) (i : ι) :
    eval z (pderiv i F) = (polynomialTranslation z F).coeff (Finsupp.single i 1) := by
  have h := constantCoeff_polynomialTranslation z (pderiv i F)
  rw [polynomialTranslation_pderiv, coeff_pderiv] at h
  simpa only [zero_add, Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one] using h.symm

theorem second_derivative_translation_coeff (z : ι → R) (F : MvPolynomial ι R) (i j : ι) :
    eval z (pderiv j (pderiv i F)) =
      (polynomialTranslation z F).coeff (Finsupp.single j 1 + Finsupp.single i 1) *
        ((Finsupp.single j 1 : ι →₀ ℕ) i + 1 : ℕ) := by
  rw [first_derivative_translation_coeff z (pderiv i F) j,
    polynomialTranslation_pderiv, coeff_pderiv, Nat.cast_add, Nat.cast_one]

theorem polynomialTranslation_totalDegree_le [Nontrivial R] (z : ι → R) (F : MvPolynomial ι R) :
    (polynomialTranslation z F).totalDegree ≤ F.totalDegree := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [polynomialTranslation, eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add, Finsupp.prod]
  apply (totalDegree_finsetProd _ _).trans
  have hlinear (i : ι) : (MvPolynomial.X i + MvPolynomial.C (z i)).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le (by rw [totalDegree_X])
    rw [totalDegree_C]
    exact Nat.zero_le _
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left (e i) (hlinear i))))
  simpa only [mul_one, Finsupp.sum] using (le_totalDegree he)

end LeanCanny.CountingHierarchy
