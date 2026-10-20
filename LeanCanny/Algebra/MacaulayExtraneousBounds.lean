/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayExtraneous
public import LeanCanny.Algebra.MacaulayPolynomialDeformationBounds
public import LeanCanny.Algebra.PrincipalPolynomialBounds

/-! # Degree and integer coefficient bounds for the extraneous deformation -/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical
variable {n : ℕ}

theorem extraneous_deformation_degree {R : Type*} [CommRing R]
    (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (extraneousPadded (deformation p d) d W).det.natDegree ≤ FixedWidthPolynomial.count n W := by
  have h := det_natDegree_le (extraneousPadded (deformation p d) d W) (fun _ => 1)
    (PrincipalPadding.entry_degree (matrix (deformation p d) d W) (extraneousIndices d W) 1
      (matrix_deformation_entry_degree_le p d W))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using h

theorem extraneous_polynomial_deformation_inner_degree
    (p : Fin n → MvPolynomial (Fin n) (Polynomial ℤ)) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i e, ((p i).coeff e).natDegree ≤ E) (j : ℕ) :
    ((extraneousPadded (deformation p d) d W).det.coeff j).natDegree ≤ FixedWidthPolynomial.count n W * E := by
  rw [extraneous_deformation_eq_affine]
  simpa only [Fintype.card_fin] using AffineCharacteristic.polynomial_inner_degree (extraneousPadded p d W) E
    (PrincipalPadding.entry_degree (matrix p d W) (extraneousIndices d W) E (polynomial_entry_degree_le p d W E hp)) j

theorem extraneous_polynomial_deformation_coefficient_size
    (p : Fin n → MvPolynomial (Fin n) (Polynomial ℤ)) (d : Fin n → ℕ) (W E b : ℕ)
    (hdeg : ∀ i e, ((p i).coeff e).natDegree ≤ E)
    (hmass : ∀ i e, coefficientMass ((p i).coeff e) ≤ 2 ^ b) (k l : ℕ) :
    (((extraneousPadded (deformation p d) d W).det.coeff l).coeff k).natAbs.size ≤
      (FixedWidthPolynomial.count n W).size * FixedWidthPolynomial.count n W +
        FixedWidthPolynomial.count n W * (b + 2) + 1 := by
  rw [extraneous_deformation_eq_affine]
  simpa only [Fintype.card_fin] using AffineCharacteristic.polynomial_coefficient_size (extraneousPadded p d W) E b
    (PrincipalPadding.entry_degree (matrix p d W) (extraneousIndices d W) E (polynomial_entry_degree_le p d W E hdeg))
    (PrincipalPadding.entry_mass (matrix p d W) (extraneousIndices d W) b (matrix_entry_mass_le p d W b hmass)) k l

end LeanCanny.Algebra.Macaulay
