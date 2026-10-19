/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.Div

/-!
# Characteristic adjugates through matrix powers

The adjugate of `X I - A` is the quotient of the scalar characteristic
polynomial by `X - A`, in the polynomial ring with matrix coefficients.
Synthetic division therefore expresses every coefficient using powers of A.
These division-free coefficient identities are ingredients of the bordered
characteristic-polynomial recurrence used by Berkowitz's algorithm.
-/

@[expose] public section

noncomputable section

namespace LeanCanny.Algebra
open Matrix Polynomial Finset

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem adjugate_charmatrix_eq_div (A : Matrix ι ι R) :
    matPolyEquiv (adjugate (charmatrix A)) =
      A.charpoly.map (algebraMap R (Matrix ι ι R)) /ₘ (X - C A) := by
  have h := congrArg matPolyEquiv (mul_adjugate (charmatrix A))
  rw [map_mul, matPolyEquiv_charmatrix, matPolyEquiv_smul_one] at h
  change (X - C A) * matPolyEquiv (adjugate (charmatrix A)) =
    A.charpoly.map (algebraMap R (Matrix ι ι R)) at h
  rw [← h, mul_divByMonic_cancel_left _ (monic_X_sub_C A)]

theorem adjugate_charmatrix_coeff_matrix (A : Matrix ι ι R) (d : ℕ) :
    (matPolyEquiv (adjugate (charmatrix A))).coeff d =
      ∑ k ∈ Icc (d + 1) (Fintype.card ι),
        A ^ (k - (d + 1)) * algebraMap R (Matrix ι ι R) (A.charpoly.coeff k) := by
  nontriviality R
  rw [adjugate_charmatrix_eq_div, coeff_divByMonic_X_sub_C]
  simp only [coeff_map]
  let p := A.charpoly.map (algebraMap R (Matrix ι ι R))
  have hp : p.natDegree ≤ Fintype.card ι :=
    natDegree_map_le.trans_eq (charpoly_natDegree_eq_dim A)
  apply sum_subset (by intro k hk; exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans hp⟩)
  · intro k hk hkn
    have hkd : (A.charpoly.map (algebraMap R (Matrix ι ι R))).natDegree < k := by
      have := mem_Icc.mp hk
      simp only [mem_Icc, not_and_or, not_le] at hkn
      omega
    rw [← coeff_map, coeff_eq_zero_of_natDegree_lt hkd, mul_zero]

theorem adjugate_charmatrix_coeff (A : Matrix ι ι R) (d : ℕ) (i j : ι) :
    (adjugate (charmatrix A) i j).coeff d =
      ∑ k ∈ Icc (d + 1) (Fintype.card ι),
        A.charpoly.coeff k * (A ^ (k - (d + 1))) i j := by
  have h := congrArg (fun M : Matrix ι ι R => M i j) (adjugate_charmatrix_coeff_matrix A d)
  simpa [matPolyEquiv_coeff_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.algebraMap_matrix_apply,
    Matrix.diagonal, mul_comm] using h

end LeanCanny.Algebra
