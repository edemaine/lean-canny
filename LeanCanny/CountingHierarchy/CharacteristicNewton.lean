/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PolynomialDeterminantDerivative
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Characteristic coefficients and multiplication power traces -/

public section

namespace LeanCanny.CountingHierarchy

open Matrix Polynomial
open scoped Classical BigOperators

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The adjugate of `1 - X M`, regarded as a polynomial of matrices. -/
@[expose] noncomputable def reverseAdjugate (M : Matrix ι ι R) : (Matrix ι ι R)[X] :=
  matPolyEquiv ((1 - (X : R[X]) • M.map C).adjugate)

theorem reverseAdjugate_relation (M : Matrix ι ι R) :
    reverseAdjugate M * (1 - X * C M) =
      M.charpolyRev.map (algebraMap R (Matrix ι ι R)) := by
  have h := congrArg (matPolyEquiv (R := R))
    (Matrix.adjugate_mul (1 - (X : R[X]) • M.map C))
  simpa only [reverseAdjugate, Matrix.charpolyRev, map_mul, map_sub, map_one,
    matPolyEquiv_map_smul, map_X, matPolyEquiv_map_C, matPolyEquiv_smul_one, mul_one] using h

theorem reverseAdjugate_coeff_zero (M : Matrix ι ι R) :
    (reverseAdjugate M).coeff 0 = algebraMap R (Matrix ι ι R) (M.charpolyRev.coeff 0) := by
  have h := congrArg (fun p : (Matrix ι ι R)[X] => p.coeff 0) (reverseAdjugate_relation M)
  simpa only [mul_sub, mul_one, ← mul_assoc, coeff_sub, coeff_mul_C,
    coeff_mul_X_zero, zero_mul, sub_zero, coeff_map] using h

theorem reverseAdjugate_coeff_succ (M : Matrix ι ι R) (k : ℕ) :
    (reverseAdjugate M).coeff (k + 1) =
      algebraMap R (Matrix ι ι R) (M.charpolyRev.coeff (k + 1)) +
        (reverseAdjugate M).coeff k * M := by
  have h := congrArg (fun p : (Matrix ι ι R)[X] => p.coeff (k + 1))
    (reverseAdjugate_relation M)
  simp only [mul_sub, mul_one, ← mul_assoc, coeff_sub, coeff_mul_C,
    coeff_mul_X, coeff_map] at h
  exact sub_eq_iff_eq_add.mp h

theorem reverseAdjugate_coeff (M : Matrix ι ι R) (k : ℕ) :
    (reverseAdjugate M).coeff k =
      ∑ j ∈ Finset.range (k + 1), M.charpolyRev.coeff (k - j) • M ^ j := by
  induction k with
  | zero => simpa [Algebra.algebraMap_eq_smul_one] using reverseAdjugate_coeff_zero M
  | succ k ih =>
    rw [reverseAdjugate_coeff_succ, ih, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, pow_zero, Nat.sub_zero]
    rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ, smul_mul_assoc]
    · exact Algebra.algebraMap_eq_smul_one _

theorem derivative_charpolyRev (M : Matrix ι ι R) :
    derivative M.charpolyRev =
      -(((1 - (X : R[X]) • M.map C).adjugate) * M.map C).trace := by
  have h := derivative_det_adjugate (1 - (X : R[X]) • M.map C)
  have hder : (1 - (X : R[X]) • M.map C).map derivative = -M.map C := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      derivative_sub, derivative_mul, derivative_X, derivative_C, one_mul,
      mul_zero, add_zero, Matrix.neg_apply]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hder, Matrix.mul_neg, Matrix.trace_neg] at h
  exact h

theorem matrix_trace_coeff (M : Matrix ι ι R[X]) (k : ℕ) :
    M.trace.coeff k = ((matPolyEquiv M).coeff k).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, finsetSum_coeff, matPolyEquiv_coeff_apply]

/-- Newton's characteristic-coefficient recurrence over an arbitrary
 commutative ring. No inverses or eigenvalues occur in this identity. -/
theorem charpolyRev_newton (M : Matrix ι ι R) (k : ℕ) :
    (k + 1 : ℕ) * M.charpolyRev.coeff (k + 1) =
      -(∑ j ∈ Finset.range (k + 1),
        M.charpolyRev.coeff (k - j) * (M ^ (j + 1)).trace) := by
  have h := congrArg (fun p : R[X] => p.coeff k) (derivative_charpolyRev M)
  rw [coeff_derivative, coeff_neg, matrix_trace_coeff, map_mul, matPolyEquiv_map_C,
    coeff_mul_C] at h
  change M.charpolyRev.coeff (k + 1) * ((k : R) + 1) =
    -((reverseAdjugate M).coeff k * M).trace at h
  rw [reverseAdjugate_coeff, Finset.sum_mul, Matrix.trace_sum] at h
  simp only [smul_mul_assoc, ← pow_succ, Matrix.trace_smul, smul_eq_mul] at h
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h

end LeanCanny.CountingHierarchy
