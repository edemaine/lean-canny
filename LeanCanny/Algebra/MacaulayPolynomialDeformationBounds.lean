/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayDeformationParameters
public import LeanCanny.Algebra.PolynomialAffineDeformation

/-! # Bounds for deformation with polynomial input coefficients

The original coefficients may already encode other independent parameters.
Their degree bound is preserved in each deformation coefficient, and their
mass allowance gains only two bits after any second coefficient encoding.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical

theorem coefficient_deformation_affine {R : Type*} [CommRing R] {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (i : Fin n) (e : Fin n →₀ ℕ) :
    (deformation p d i).coeff e = PolynomialAffineDeformation.affine ((p i).coeff e)
      (if Finsupp.single i (d i) = e then (1 : R) else 0) := by
  rw [coefficient_deformation, PolynomialAffineDeformation.affine]
  split_ifs <;> simp only [Polynomial.C_1, Polynomial.C_0]

theorem det_polynomial_deformation_coefficient_size_le {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) (Polynomial ℤ)) (d : Fin n → ℕ) (W E b : ℕ)
    (hdeg : ∀ i e, ((p i).coeff e).natDegree ≤ E)
    (hmass : ∀ i e, coefficientMass ((p i).coeff e) ≤ 2 ^ b) (k l : ℕ) :
    ((((matrix (deformation p d) d W).det.coeff l).coeff k).natAbs.size) ≤
      (FixedWidthPolynomial.count n W).size * FixedWidthPolynomial.count n W + FixedWidthPolynomial.count n W * (b + 2) + 1 := by
  apply det_bivariate_coefficient_size_le _ d W E (b + 2)
  · intro i e j
    rw [coefficient_deformation_affine]
    exact PolynomialAffineDeformation.inner_degree_le _ _ E (hdeg i e) j
  · intro B i e
    rw [coefficient_deformation_affine]
    apply PolynomialAffineDeformation.encoded_mass_le _ _ B b (hmass i e)
    split_ifs <;> decide

end LeanCanny.Algebra.Macaulay
