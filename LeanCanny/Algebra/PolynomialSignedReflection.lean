/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Lowest coefficients under parameter sign reversal

Replacing X by -X preserves the lowest nonzero order and multiplies that
coefficient by (-1) raised to the order. The result needs no domain assumption.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialSignedReflection
open Polynomial

variable {R : Type*} [CommRing R]

theorem sign_mul_eq_zero_iff (n : ℕ) (a : R) : (-1 : R) ^ n * a = 0 ↔ a = 0 := by
  exact (isUnit_neg_one.pow n).mul_right_eq_zero

theorem coefficient (p : Polynomial R) (k : ℕ) : (p.comp (-Polynomial.X)).coeff k = (-1 : R) ^ k * p.coeff k := by
  simpa only [map_neg, map_one, neg_one_mul, mul_comm] using
    (Polynomial.comp_C_mul_X_coeff (p := p) (r := (-1 : R)) (n := k))

theorem preserves_lowest (p : Polynomial R) :
    (p.comp (-Polynomial.X)).natTrailingDegree = p.natTrailingDegree ∧
      (p.comp (-Polynomial.X)).trailingCoeff = (-1 : R) ^ p.natTrailingDegree * p.trailingCoeff := by
  by_cases hp : p = 0
  · simp [hp]
  have hc : (p.comp (-Polynomial.X)).coeff p.natTrailingDegree ≠ 0 := by
    rw [coefficient, ne_eq, sign_mul_eq_zero_iff]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp
  have hpn : p.comp (-Polynomial.X) ≠ 0 := by
    intro hz
    exact hc (by rw [hz, Polynomial.coeff_zero])
  have he : (p.comp (-Polynomial.X)).natTrailingDegree = p.natTrailingDegree := by
    apply le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hc)
    apply Polynomial.le_natTrailingDegree hpn
    intro i hi
    rw [coefficient, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi, mul_zero]
  refine ⟨he, ?_⟩
  simp only [Polynomial.trailingCoeff, he, coefficient]

end LeanCanny.Algebra.PolynomialSignedReflection
