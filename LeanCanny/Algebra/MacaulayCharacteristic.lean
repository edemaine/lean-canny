/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayAffineDeformation
public import LeanCanny.Algebra.AffineCharacteristic

/-! # The padded Macaulay deformation and characteristic numerator

The existing interpolation determinant has the same lowest order as det(A-sI).
Their lowest coefficients differ by (-1) raised to that order. The latter
determinant is the ordinary characteristic polynomial times the dimension sign.
No identification with the resultant quotient is asserted here.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open Polynomial

variable {n : ℕ} {R : Type*} [CommRing R]

theorem matrix_deformation_eq_affine (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    matrix (deformation p d) d W = AffineCharacteristic.affineMatrix (matrix p d W) := by
  funext r s
  exact matrix_deformation_entry p d W r s

noncomputable def characteristicNumerator (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) : Polynomial R :=
  (AffineCharacteristic.subtractiveMatrix (matrix p d W)).det

theorem characteristicNumerator_eq_charpoly (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    characteristicNumerator p d W = (-1 : Polynomial R) ^ FixedWidthPolynomial.count n W * (matrix p d W).charpoly := by
  simpa only [characteristicNumerator, Fintype.card_fin] using AffineCharacteristic.subtractive_det_eq_charpoly (matrix p d W)

theorem characteristicNumerator_lowest (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (characteristicNumerator p d W).natTrailingDegree = (matrix (deformation p d) d W).det.natTrailingDegree ∧
      (characteristicNumerator p d W).trailingCoeff =
        (-1 : R) ^ (matrix (deformation p d) d W).det.natTrailingDegree * (matrix (deformation p d) d W).det.trailingCoeff := by
  rw [matrix_deformation_eq_affine]
  exact AffineCharacteristic.subtractive_lowest (matrix p d W)

theorem characteristicNumerator_lowest_eval_zero_iff {K : Type*} [CommRing K]
    (φ : R →+* K) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    φ (characteristicNumerator p d W).trailingCoeff = 0 ↔ φ (matrix (deformation p d) d W).det.trailingCoeff = 0 := by
  rw [(characteristicNumerator_lowest p d W).2, map_mul, map_pow, map_neg, map_one,
    PolynomialSignedReflection.sign_mul_eq_zero_iff]

end LeanCanny.Algebra.Macaulay
