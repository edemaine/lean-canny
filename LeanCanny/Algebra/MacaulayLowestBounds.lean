/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CharacteristicLowestBounds
public import LeanCanny.Algebra.MacaulayPolynomialDeformationBounds

/-! # Bounded lowest numerator polynomials for parameterized systems

The padded Macaulay matrix gives a concrete nonzero polynomial in the retained
parameter. Its degree and integer coefficient budgets depend explicitly on
the fixed-width matrix count and the original source coefficient budgets.
Annihilation at regular roots is supplied by analytic persistence.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayLowestBounds
open Polynomial

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def polynomial (p : Fin n → MvPolynomial (Fin n) (Polynomial R))
    (d : Fin n → ℕ) (W : ℕ) : Polynomial R :=
  CharacteristicLowestBounds.lowest (Macaulay.matrix p d W)

theorem polynomial_eq (p : Fin n → MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (W : ℕ) :
    polynomial p d W = (Macaulay.characteristicNumerator p d W).trailingCoeff := rfl

theorem ne_zero [IsDomain R] (p : Fin n → MvPolynomial (Fin n) (Polynomial R))
    (d : Fin n → ℕ) (W : ℕ) : polynomial p d W ≠ 0 :=
  CharacteristicLowestBounds.lowest_ne_zero _

theorem degree_le (p : Fin n → MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i e, ((p i).coeff e).natDegree ≤ E) :
    (polynomial p d W).natDegree ≤ FixedWidthPolynomial.count n W * E := by
  simpa only [polynomial, Fintype.card_fin] using CharacteristicLowestBounds.degree_le _ E
    (Macaulay.polynomial_entry_degree_le p d W E hp)

omit [CommRing R] in
theorem mass_le (p : Fin n → MvPolynomial (Fin n) (Polynomial ℤ)) (d : Fin n → ℕ) (W b : ℕ)
    (hp : ∀ i e, coefficientMass ((p i).coeff e) ≤ 2 ^ b) :
    coefficientMass (polynomial p d W) ≤
      (FixedWidthPolynomial.count n W).factorial * (2 ^ b + 1) ^ FixedWidthPolynomial.count n W := by
  simpa only [polynomial, Fintype.card_fin] using CharacteristicLowestBounds.mass_le _ (2 ^ b)
    (Macaulay.matrix_entry_mass_le p d W b hp)

omit [CommRing R] in
theorem coefficient_size_le (p : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (d : Fin n → ℕ) (W b : ℕ)
    (hp : ∀ i e, coefficientMass ((p i).coeff e) ≤ 2 ^ b) (k : ℕ) :
    ((polynomial p d W).coeff k).natAbs.size ≤
      (FixedWidthPolynomial.count n W).size * FixedWidthPolynomial.count n W +
        FixedWidthPolynomial.count n W * (b + 1) + 1 := by
  simpa only [polynomial, Fintype.card_fin] using CharacteristicLowestBounds.coefficient_size_le _ b
    (Macaulay.matrix_entry_mass_le p d W b hp) k

end LeanCanny.Algebra.MacaulayLowestBounds
