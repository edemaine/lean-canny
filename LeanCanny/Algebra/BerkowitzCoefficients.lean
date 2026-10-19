/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzRecurrence

/-!
# A recursive reference for characteristic coefficients and the determinant

The bordered recurrence is specialized to the leading row and column of a
`Fin n` matrix. A structural recursion computes each characteristic coefficient
from smaller principal matrices and scalar matrix-power moments. Its constant
coefficient recovers the determinant, including the empty matrix.

This function is an algebraic correctness reference. Its recursion has linear
depth in the dimension; no complexity bound is claimed. Balanced products of
coefficient transformations and a streamed implementation are still needed.
-/

@[expose] public section

noncomputable section

namespace LeanCanny.Algebra.Berkowitz
open Matrix Polynomial Finset

variable {R : Type*} [CommRing R]

def headTailEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun
    | .inl _ => 0
    | .inr i => i.succ
  invFun := Fin.cases (.inl ()) (fun i => .inr i)
  left_inv x := by cases x <;> rfl
  right_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem charpoly_coeff_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (d : ℕ) :
    A.charpoly.coeff d =
      (if d = 0 then 0 else (A.submatrix Fin.succ Fin.succ).charpoly.coeff (d - 1)) -
        A 0 0 * (A.submatrix Fin.succ Fin.succ).charpoly.coeff d -
        ∑ k ∈ Icc (d + 1) n, (A.submatrix Fin.succ Fin.succ).charpoly.coeff k *
          borderMoment (fun i => A 0 i.succ) (fun i => A i.succ 0)
            (A.submatrix Fin.succ Fin.succ) (k - (d + 1)) := by
  have heq : A.submatrix (headTailEquiv n) (headTailEquiv n) =
      border (A 0 0) (fun i => A 0 i.succ) (fun i => A i.succ 0)
        (A.submatrix Fin.succ Fin.succ) := by
    ext (⟨⟩ | i) (⟨⟩ | j) <;> simp [border, headTailEquiv]
  have h := Matrix.charpoly_reindex (headTailEquiv n).symm A
  change (A.submatrix (headTailEquiv n) (headTailEquiv n)).charpoly = A.charpoly at h
  rw [heq] at h
  rw [← h, charpoly_border_coeff]
  simp only [Fintype.card_fin]

def coefficients : {n : ℕ} → Matrix (Fin n) (Fin n) R → ℕ → R
  | 0, _, d => if d = 0 then 1 else 0
  | n + 1, A, d =>
      let D := A.submatrix Fin.succ Fin.succ
      (if d = 0 then 0 else coefficients D (d - 1)) - A 0 0 * coefficients D d -
        ∑ k ∈ Icc (d + 1) n, coefficients D k *
          borderMoment (fun i => A 0 i.succ) (fun i => A i.succ 0) D (k - (d + 1))

theorem coefficients_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (d : ℕ) :
    coefficients A d = A.charpoly.coeff d := by
  induction n generalizing d with
  | zero => simp [coefficients, coeff_one]
  | succ n ih =>
      rw [coefficients, charpoly_coeff_succ]
      simp_rw [ih]

def determinant {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : R := (-1) ^ n * coefficients A 0

theorem determinant_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : determinant A = A.det := by
  rw [determinant, coefficients_eq, Matrix.det_eq_sign_charpoly_coeff]
  simp only [Fintype.card_fin]

end LeanCanny.Algebra.Berkowitz
