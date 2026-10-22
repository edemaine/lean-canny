/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ScaledSquarefree

/-! # Square-free preprocessing preserves the padding polynomial X -/

@[expose] public section

namespace LeanCanny.Algebra.ScaledSquarefree
open Polynomial

theorem degree_X : degree (X : ℤ[X]) = 0 := by
  simp only [degree, PolynomialGCDBits.degree, derivative_X, Polynomial.map_X, Polynomial.map_one]
  have h := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right (X : ℚ[X]) 1) (one_ne_zero : (1 : ℚ[X]) ≠ 0)
  simp only [natDegree_one] at h
  omega

theorem gcd_X : gcd (X : ℤ[X]) = 1 := by
  have hd : PolynomialGCDBits.degree (X : ℤ[X]) 1 = (1 : ℤ[X]).natDegree := by
    simpa only [degree, derivative_X, natDegree_one] using degree_X
  rw [gcd, derivative_X, PolynomialGCDBits.representative_terminal _ _ hd (by simp)]
  simp

theorem polynomial_X : polynomial (X : ℤ[X]) = X := by
  rw [polynomial, gcd_X, degree_X, natDegree_X, Nat.sub_zero]
  simpa using ScaledPolynomialQuotient.quotient_mul (1 : ℤ[X]) X 0 1 (by simp) (by simp)

end LeanCanny.Algebra.ScaledSquarefree
