/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedCharacteristicQuotientMass
public import LeanCanny.Algebra.MacaulayFixedPaddedPolynomialValue
public import LeanCanny.Algebra.MacaulayBounds

/-! # Input-derived mass of the normalized Macaulay polynomial value

The full padded matrices and a monic characteristic divisor give an actual
coefficient bound. No extraneous determinant survival premise is needed.
-/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayNormalizedPolynomialMass
open Polynomial
open scoped Classical

theorem normalized_value {n : ℕ}
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℤ[X])
    (d : Fin (n + 1) → ℕ) (W H : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (hhom : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hp : ∀ i e, coefficientMass ((p i).coeff e) ≤ 2 ^ H) :
    coefficientMass (MacaulayUniversal.polynomialValue d W hdegree hW p) ≤
      2 ^ PaddedCharacteristicQuotientMass.budget (FixedWidthPolynomial.count (n + 1) W)
        (FixedWidthPolynomial.count (n + 1) W) H := by
  rw [MacaulayFixedPaddedPolynomialValue.value_eq_coefficient_zero d W hdegree hW p hhom hd]
  have hA := Macaulay.matrix_entry_mass_le p d W H hp
  have hE : ∀ i j, coefficientMass (Macaulay.extraneousPadded p d W i j) ≤ 2 ^ H := by
    intro i j
    simp only [Macaulay.extraneousPadded, PrincipalPadding.matrix]
    split_ifs
    · exact hA i j
    · rw [Matrix.one_apply]
      split_ifs
      · change coefficientMass (Polynomial.C (1 : ℤ)) ≤ 2 ^ H
        rw [coefficientMass_C]
        exact Nat.one_le_two_pow
      · simp
  exact PaddedCharacteristicQuotientMass.coefficient
    (FixedWidthPolynomial.count (n + 1) W) (FixedWidthPolynomial.count (n + 1) W) H
    (Macaulay.matrix p d W) (Macaulay.extraneousPadded p d W) hA hE 0

end LeanCanny.Algebra.MacaulayNormalizedPolynomialMass
