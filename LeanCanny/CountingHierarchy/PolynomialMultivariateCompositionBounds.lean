/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MvCoefficientMass
public import LeanCanny.Algebra.CoefficientMass
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Degree and coefficient-mass budgets for polynomial substitution

These bounds apply to a univariate integer polynomial evaluated at an integer
multivariate polynomial, as in the second quotient determinant construction.
-/

public section

namespace LeanCanny.CountingHierarchy

open LeanCanny.Algebra
open scoped BigOperators Classical

variable {ι : Type*}

theorem polynomial_aeval_mass_le (p : Polynomial ℤ) (v : MvPolynomial ι ℤ) (D M : ℕ)
    (hD : p.natDegree ≤ D) (hM : 1 ≤ M) (hv : MvMass.mass v ≤ M) :
    MvMass.mass (Polynomial.aeval v p) ≤ coefficientMass p * M ^ D := by
  rw [Polynomial.aeval_def, MvPolynomial.algebraMap_eq,
    Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply (MvMass.sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ p.support, (p.coeff i).natAbs * M ^ D := by
      apply Finset.sum_le_sum
      intro i hi
      apply (MvMass.mul_le _ _).trans
      rw [MvMass.C]
      apply Nat.mul_le_mul_left
      exact (MvMass.pow_le v i).trans
        ((Nat.pow_le_pow_left hv i).trans
          (Nat.pow_le_pow_right hM ((Polynomial.le_natDegree_of_mem_supp i hi).trans hD)))
    _ = _ := by rw [coefficientMass, Polynomial.sum_def, Finset.sum_mul]

theorem polynomial_aeval_mass_le_pow (p : Polynomial ℤ) (v : MvPolynomial ι ℤ)
    (D bp bv : ℕ) (hD : p.natDegree ≤ D)
    (hp : coefficientMass p ≤ 2 ^ bp) (hv : MvMass.mass v ≤ 2 ^ bv) :
    MvMass.mass (Polynomial.aeval v p) ≤ 2 ^ (bp + D * bv) := by
  apply (polynomial_aeval_mass_le p v D (2 ^ bv) hD Nat.one_le_two_pow hv).trans
  exact (Nat.mul_le_mul_right _ hp).trans_eq (by rw [← pow_mul, ← pow_add, Nat.mul_comm D])

theorem polynomial_aeval_degree_le (p : Polynomial ℤ) (v : MvPolynomial ι ℤ)
    (D Ω : ℕ) (hD : p.natDegree ≤ D) (hv : v.totalDegree ≤ Ω) :
    (Polynomial.aeval v p).totalDegree ≤ D * Ω := by
  rw [Polynomial.aeval_def, MvPolynomial.algebraMap_eq,
    Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_pow v i).trans
    (Nat.mul_le_mul ((Polynomial.le_natDegree_of_mem_supp i hi).trans hD) hv)

end LeanCanny.CountingHierarchy
