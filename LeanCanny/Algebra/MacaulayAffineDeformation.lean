/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayDeformation

/-! # The deformation matrix is affine in the original matrix

Identity padding and coordinate powers agree, so the full padded matrix is
A + parameter*(I-A). Its parameter coefficients require only one original
matrix entry and the diagonal test, rather than deformed source coefficients.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open MvPolynomial

variable {n : ℕ} {R : Type*} [CommRing R]

theorem matrix_deformation_entry (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (r s : Index n W) : matrix (deformation p d) d W r s =
      Polynomial.C (matrix p d W r s) + Polynomial.X *
        (Polynomial.C ((1 : Matrix (Index n W) (Index n W) R) r s) - Polynomial.C (matrix p d W r s)) := by
  have hI : (1 : Matrix (Index n W) (Index n W) (Polynomial R)) r s =
      Polynomial.C ((1 : Matrix (Index n W) (Index n W) R) r s) := by
    by_cases h : r = s <;> simp [Matrix.one_apply, h]
  by_cases hr : (FixedWidthPolynomial.vector n W r).degree = level d
  · have hpw := congrArg (fun A : Matrix (Index n W) (Index n W) (Polynomial R) => A r s)
      (matrix_powers (R := Polynomial R) d W)
    rw [entry_active _ d W r s hr] at hpw
    by_cases hg : remainder d (FixedWidthPolynomial.vector n W r) hr ≤ FixedWidthPolynomial.vector n W s
    · rw [ite_eq_left hg] at hpw
      simp only [powers, MvPolynomial.coeff_monomial] at hpw
      rw [entry_active _ d W r s hr, ite_eq_left hg, coefficient_deformation, hpw, hI]
      simp only [entry_active p d W r s hr, ite_eq_left hg]
    · rw [ite_eq_right hg] at hpw
      rw [entry_active _ d W r s hr, ite_eq_right hg]
      simp only [entry_active p d W r s hr, ite_eq_right hg, Polynomial.C_0, sub_zero, zero_add]
      rw [← hI, ← hpw, mul_zero]
  · simp only [matrix, dite_eq_right hr, sub_self, mul_zero, add_zero]
    exact hI

theorem matrix_deformation_coefficient (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (r s : Index n W) (D : ℕ) : (matrix (deformation p d) d W r s).coeff D =
      if D = 0 then matrix p d W r s else
        if D = 1 then (1 : Matrix (Index n W) (Index n W) R) r s - matrix p d W r s else 0 := by
  rw [matrix_deformation_entry, ← map_sub Polynomial.C]
  cases D with
  | zero => simp
  | succ k =>
    cases k with
    | zero => simp
    | succ k => simp [Polynomial.coeff_X_mul]

end LeanCanny.Algebra.Macaulay
