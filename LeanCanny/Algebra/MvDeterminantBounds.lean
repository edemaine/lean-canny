/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MvCoefficientMass
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Nat.Size

/-! # Degree and integer mass bounds for multivariate determinants -/

@[expose] public section
namespace LeanCanny.Algebra.MvDeterminantBounds
open MvPolynomial
open scoped BigOperators Classical

theorem degree_le {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ ℤ)) (D : ℕ) (hD : ∀ i j, (A i j).totalDegree ≤ D) :
    A.det.totalDegree ≤ Fintype.card ι * D := by
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro π _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  exact (Finset.sum_le_sum (fun j _ => hD (π j) j)).trans_eq (by simp)

theorem mass_le {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ ℤ)) (M : ℕ) (hM : ∀ i j, MvMass.mass (A i j) ≤ M) :
    MvMass.mass A.det ≤ (Fintype.card ι).factorial * M ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ π : Equiv.Perm ι, MvMass.mass (Equiv.Perm.sign π • ∏ j, A (π j) j) := MvMass.sum_le _ _
    _ ≤ ∑ _π : Equiv.Perm ι, ∏ _j : ι, M := by
      apply Finset.sum_le_sum
      intro π _
      rw [Units.smul_def, MvPolynomial.smul_eq_C_mul]
      apply (MvMass.mul_le _ _).trans
      rw [MvMass.C, Int.units_natAbs, one_mul]
      exact (MvMass.prod_le _ _).trans (Finset.prod_le_prod fun j _ => hM (π j) j)
    _ = _ := by simp [Fintype.card_perm]

theorem mass_le_pow {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ ℤ)) (b : ℕ) (hM : ∀ i j, MvMass.mass (A i j) ≤ 2 ^ b) :
    MvMass.mass A.det ≤ 2 ^ ((Fintype.card ι).size * Fintype.card ι + Fintype.card ι * b) := by
  have hf : (Fintype.card ι).factorial ≤ 2 ^ ((Fintype.card ι).size * Fintype.card ι) :=
    (Nat.factorial_le_pow _).trans
      ((Nat.pow_le_pow_left (Nat.lt_size_self _).le _).trans_eq (pow_mul _ _ _).symm)
  exact (mass_le A (2 ^ b) hM).trans ((Nat.mul_le_mul_right _ hf).trans_eq (by
    rw [← pow_mul, ← pow_add, Nat.mul_comm b]))

end LeanCanny.Algebra.MvDeterminantBounds
