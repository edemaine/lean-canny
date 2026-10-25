/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.WeightedHomogenization
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Additive operations in the explicit weighted homogenization

The coefficient formula makes homogenization additive even when high-degree
terms are discarded. Constants act coefficientwise. For unit weights, a pure
power already at the target degree only renames its variable.
-/

@[expose] public section
namespace LeanCanny.Algebra.WeightedHomogenization
open MvPolynomial
open scoped Classical BigOperators

variable {σ R : Type*} [Fintype σ] [CommRing R]

theorem homogenize_zero (w : σ → ℕ) (D : ℕ) : homogenize w D (0 : MvPolynomial σ R) = 0 := by
  ext m
  simp [coefficient]

theorem homogenize_add (w : σ → ℕ) (D : ℕ) (p q : MvPolynomial σ R) :
    homogenize w D (p + q) = homogenize w D p + homogenize w D q := by
  ext m
  simp only [coefficient, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  split_ifs <;> simp

theorem homogenize_sub (w : σ → ℕ) (D : ℕ) (p q : MvPolynomial σ R) :
    homogenize w D (p - q) = homogenize w D p - homogenize w D q := by
  ext m
  simp only [coefficient, coeff_sub]
  split_ifs <;> simp

theorem homogenize_C_mul (w : σ → ℕ) (D : ℕ) (a : R) (p : MvPolynomial σ R) :
    homogenize w D (C a * p) = C a * homogenize w D p := by
  ext m
  simp only [coefficient, coeff_C_mul]
  split_ifs <;> simp

theorem homogenize_sum {ι : Type*} (w : σ → ℕ) (D : ℕ) (s : Finset ι) (p : ι → MvPolynomial σ R) :
    homogenize w D (∑ i ∈ s, p i) = ∑ i ∈ s, homogenize w D (p i) := by
  induction s using Finset.induction_on with
  | empty => simp [homogenize_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, homogenize_add, ih]

theorem homogenize_monomial (w : σ → ℕ) (D : ℕ) (e : σ →₀ ℕ) (a : R) :
    homogenize w D (monomial e a) =
      if Finsupp.weight w e ≤ D then monomial (exponent w D e) a else 0 := by
  by_cases ha : a = 0
  · simp [ha, homogenize_zero]
  · simp only [homogenize, support_monomial, ha, ite_false, Finset.filter_singleton,
      coeff_monomial]
    split_ifs <;> simp

theorem homogenize_X_pow (i : σ) (D : ℕ) :
    homogenize (fun _ => 1) D (X i ^ D : MvPolynomial σ R) = X (some i) ^ D := by
  rw [X_pow_eq_monomial, homogenize_monomial]
  simp only [Finsupp.weight_single, smul_eq_mul, mul_one, le_refl, ite_true]
  have he : exponent (fun _ : σ => 1) D (Finsupp.single i D) = Finsupp.single (some i) D := by
    ext j
    cases j <;> simp [exponent, Finsupp.weight_single, Finsupp.single_apply]
  rw [he, ← X_pow_eq_monomial]

end LeanCanny.Algebra.WeightedHomogenization
