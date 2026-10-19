/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BorderedDeterminant
public import LeanCanny.Algebra.CharacteristicAdjugate

/-!
# The division-free bordered characteristic-polynomial recurrence

For a matrix bordered by scalar `a`, row `r`, and column `c`, the new
characteristic polynomial is `(X-a) χ_A - r adj(XI-A) c`. Every coefficient
of the correction is a convolution of characteristic coefficients with
the scalar moments `r A^k c`. These identities hold over any commutative
ring. Balanced products, encoded evaluation, and workspace certification
of the resulting determinant algorithm are separate obligations.
-/

@[expose] public section

noncomputable section

namespace LeanCanny.Algebra
open Matrix Polynomial Finset

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

def borderMoment (r c : ι → R) (A : Matrix ι ι R) (k : ℕ) : R := r ⬝ᵥ (A ^ k *ᵥ c)

theorem charmatrix_border (a : R) (r c : ι → R) (A : Matrix ι ι R) :
    charmatrix (border a r c A) =
      border (X - C a) (fun i => -C (r i)) (fun i => -C (c i)) (charmatrix A) := by
  ext (⟨⟩ | i) (⟨⟩ | j) <;>
    simp [border, charmatrix, Matrix.diagonal, sub_eq_add_neg]

theorem charpoly_border (a : R) (r c : ι → R) (A : Matrix ι ι R) :
    (border a r c A).charpoly = (X - C a) * A.charpoly -
      (fun i => C (r i)) ⬝ᵥ (adjugate (charmatrix A) *ᵥ fun i => C (c i)) := by
  rw [charpoly, charmatrix_border,
    det_border_of_isRegular _ _ _ _ A.charpoly_monic.isRegular]
  simp [charpoly, dotProduct, mulVec]

theorem border_correction_coeff (r c : ι → R) (A : Matrix ι ι R) (d : ℕ) :
    ((fun i => C (r i)) ⬝ᵥ (adjugate (charmatrix A) *ᵥ fun i => C (c i))).coeff d =
      ∑ k ∈ Icc (d + 1) (Fintype.card ι),
        A.charpoly.coeff k * borderMoment r c A (k - (d + 1)) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, finsetSum_coeff, coeff_C_mul,
    coeff_mul_C, adjugate_charmatrix_coeff]
  simp only [borderMoment, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  trans ∑ k ∈ Icc (d + 1) (Fintype.card ι), ∑ i, ∑ j,
    r i * (A.charpoly.coeff k * (A ^ (k - (d + 1))) i j * c j)
  · calc
      _ = ∑ i, ∑ k ∈ Icc (d + 1) (Fintype.card ι), ∑ j,
          r i * (A.charpoly.coeff k * (A ^ (k - (d + 1))) i j * c j) := by
        apply sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  · apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring

theorem charpoly_border_coeff (a : R) (r c : ι → R) (A : Matrix ι ι R) (d : ℕ) :
    (border a r c A).charpoly.coeff d =
      (if d = 0 then 0 else A.charpoly.coeff (d - 1)) - a * A.charpoly.coeff d -
        ∑ k ∈ Icc (d + 1) (Fintype.card ι),
          A.charpoly.coeff k * borderMoment r c A (k - (d + 1)) := by
  rw [charpoly_border, coeff_sub, border_correction_coeff, sub_mul, coeff_sub, coeff_C_mul]
  congr 2
  cases d <;> simp

end LeanCanny.Algebra
