/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayExtraneous
public import LeanCanny.Algebra.PrincipalCharacteristic

/-! # The actual degree-level Macaulay characteristic numerator

The computational matrix includes identity rows outside the Macaulay level.
The true degree-level principal matrix removes exactly those rows and columns.
Its characteristic determinant differs by a power of `1-X`, and hence has the
same lowest order and coefficient as the computational numerator.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def activeIndices (d : Fin n → ℕ) (W : ℕ) : Finset (Index n W) :=
  Finset.univ.filter (fun r => (FixedWidthPolynomial.vector n W r).degree = level d)

theorem mem_activeIndices (d : Fin n → ℕ) (W : ℕ) (r : Index n W) :
    r ∈ activeIndices d W ↔ (FixedWidthPolynomial.vector n W r).degree = level d := by
  simp only [activeIndices, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def activeMinor (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :=
  (matrix p d W).submatrix (fun i : activeIndices d W => i.val) (fun i : activeIndices d W => i.val)

theorem matrix_active_padding (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    PrincipalPadding.matrix (matrix p d W) (activeIndices d W) = matrix p d W := by
  funext r s
  by_cases hr : (FixedWidthPolynomial.vector n W r).degree = level d
  · simp only [PrincipalPadding.matrix, (mem_activeIndices d W r).mpr hr, ite_true]
  · simp only [PrincipalPadding.matrix, (mem_activeIndices d W r).not.mpr hr, ite_false, matrix, dite_eq_right hr]

noncomputable def activeCharacteristic (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) : Polynomial R :=
  (AffineCharacteristic.subtractiveMatrix (activeMinor p d W)).det

theorem characteristicNumerator_eq_padding_mul_active (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    characteristicNumerator p d W = (1 - Polynomial.X : Polynomial R) ^ (activeIndices d W)ᶜ.card * activeCharacteristic p d W := by
  have h := PrincipalPadding.subtractive_determinant (matrix p d W) (activeIndices d W)
  rw [matrix_active_padding] at h
  exact h

theorem characteristicNumerator_lowest_active (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (characteristicNumerator p d W).natTrailingDegree = (activeCharacteristic p d W).natTrailingDegree ∧
      (characteristicNumerator p d W).trailingCoeff = (activeCharacteristic p d W).trailingCoeff := by
  have h := PrincipalPadding.characteristic_lowest (matrix p d W) (activeIndices d W)
  rw [matrix_active_padding] at h
  exact h

theorem extraneousIndices_subset_active (d : Fin n → ℕ) (W : ℕ) : extraneousIndices d W ⊆ activeIndices d W := by
  intro r hr
  exact (mem_activeIndices d W r).mpr ((mem_extraneousIndices d W r).mp hr).1

end LeanCanny.Algebra.Macaulay
