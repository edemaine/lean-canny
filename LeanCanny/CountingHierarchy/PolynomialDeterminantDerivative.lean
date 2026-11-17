/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Jacobi's identity for polynomial matrices over a commutative ring -/

public section

namespace LeanCanny.CountingHierarchy

open Matrix Polynomial
open scoped Classical BigOperators

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Differentiate a polynomial determinant one column at a time. -/
theorem derivative_det_columns (M : Matrix ι ι R[X]) :
    derivative M.det = ∑ i, (M.updateCol i (fun j => derivative (M j i))).det := by
  rw [Matrix.det_apply, derivative_sum]
  simp_rw [derivative_smul, derivative_prod_finset, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro π _
  congr 1
  have heq : (fun j => M.updateCol i (fun k => derivative (M k i)) (π j) j) =
      Function.update (fun j => M (π j) j) i (derivative (M (π i) i)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [heq, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase, mul_comm]

/-- Polynomial Jacobi identity, with no invertibility or characteristic
 assumption. -/
theorem derivative_det_adjugate (M : Matrix ι ι R[X]) :
    derivative M.det = (M.adjugate * M.map derivative).trace := by
  rw [derivative_det_columns, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

end LeanCanny.CountingHierarchy
