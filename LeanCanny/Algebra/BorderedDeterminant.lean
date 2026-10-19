/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Bordered determinants without inversion

A block elimination matrix proves the adjugate formula for a bordered
determinant when the smaller determinant is regular. In particular, the
determinant of a characteristic matrix is monic and can be cancelled over
any commutative coefficient ring, including rings with zero divisors.
-/

@[expose] public section

noncomputable section

namespace LeanCanny.Algebra
open Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

def border (a : R) (r c : ι → R) (D : Matrix ι ι R) : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R :=
  fromBlocks (a • (1 : Matrix Unit Unit R)) (replicateRow Unit r) (replicateCol Unit c) D

theorem det_border_of_isRegular (a : R) (r c : ι → R) (D : Matrix ι ι R)
    (hD : IsRegular D.det) :
    (border a r c D).det = a * D.det - r ⬝ᵥ (D.adjugate *ᵥ c) := by
  let B := replicateRow Unit r
  let C := replicateCol Unit c
  let P := fromBlocks (D.det • (1 : Matrix Unit Unit R)) (-(B * D.adjugate))
    (0 : Matrix ι Unit R) (1 : Matrix ι ι R)
  have hprod : P * border a r c D =
      fromBlocks (D.det • (a • (1 : Matrix Unit Unit R)) - B * D.adjugate * C) 0 C D := by
    dsimp only [P, border]
    rw [fromBlocks_multiply]
    congr 1
    · simp [B, C, Matrix.neg_mul, sub_eq_add_neg, smul_smul, mul_comm]
    · simp [B, Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_assoc, adjugate_mul, Matrix.mul_smul]
    · simp [C]
    · simp
  have hdet := congrArg Matrix.det hprod
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at hdet
  apply hD.left
  simp [B, C, det_unique, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Finset.mul_sum, mul_comm, mul_left_comm] at hdet
  rw [Finset.sum_comm] at hdet
  simpa [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hdet

end LeanCanny.Algebra
