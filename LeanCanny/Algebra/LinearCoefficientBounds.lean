/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.LinearCoefficientSpace
public import LeanCanny.Algebra.CoefficientMass

/-! # Coefficient mass after mapping a linear spatial polynomial

The coefficient of each coordinate monomial contributes at most one supplied
scalar mass. Summing these allowances bounds every collected coefficient.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial
open scoped BigOperators Classical

@[simp] theorem coefficientMass_X_pow (n : ℕ) : coefficientMass ((Polynomial.X : Polynomial ℤ) ^ n) = 1 := by
  simpa only [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_1, one_mul, Int.natAbs_one] using
    coefficientMass_monomial n (1 : ℤ)

theorem LinearCoefficientBits.coefficient_mass_le (A : List Bool → ℕ) (a : List Bool → ℕ → Polynomial ℤ)
    (c : List Bool) (φ : Polynomial ℤ →+* Polynomial ℤ) (H : ℕ)
    (h : ∀ i, i < A c → coefficientMass (φ (a c i)) ≤ H) (e : Fin (A c) →₀ ℕ) :
    coefficientMass (φ ((LinearCoefficientBits.polynomial A a c).coeff e)) ≤ A c * H := by
  rw [LinearCoefficientBits.polynomial_eq_sum, MvPolynomial.coeff_sum, map_sum]
  calc
    _ ≤ ∑ i : Fin (A c), coefficientMass (φ ((MvPolynomial.C (a c i.val) * MvPolynomial.X i).coeff e)) :=
      coefficientMass_sum_le _ _
    _ ≤ ∑ _i : Fin (A c), H := by
      apply Finset.sum_le_sum
      intro i _
      rw [MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.coeff_monomial]
      split_ifs
      · exact h i.val i.isLt
      · simp
    _ = _ := by simp

theorem LinearCoefficientBits.coefficient_natDegree_le (A : List Bool → ℕ) (a : List Bool → ℕ → Polynomial ℤ)
    (c : List Bool) (D : ℕ) (h : ∀ i, i < A c → (a c i).natDegree ≤ D) (e : Fin (A c) →₀ ℕ) :
    ((LinearCoefficientBits.polynomial A a c).coeff e).natDegree ≤ D := by
  rw [LinearCoefficientBits.polynomial_eq_sum, MvPolynomial.coeff_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  rw [MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.coeff_monomial]
  split_ifs
  · exact h i.val i.isLt
  · simp

end LeanCanny.Algebra
