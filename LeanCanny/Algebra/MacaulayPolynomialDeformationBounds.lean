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

theorem polynomial_entry_degree_le {R : Type*} [CommRing R] {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i e, ((p i).coeff e).natDegree ≤ E) (r s : Index n W) :
    (matrix p d W r s).natDegree ≤ E := by
  by_cases hr : (FixedWidthPolynomial.vector n W r).degree = level d
  · rw [entry_active p d W r s hr]
    split_ifs
    · exact hp _ _
    · simp
  · simp only [matrix, dite_eq_right hr]
    change (if r = s then (1 : Polynomial R) else 0).natDegree ≤ E
    split_ifs <;> simp

theorem polynomial_deformation_entry_inner_degree {R : Type*} [CommRing R] {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i e, ((p i).coeff e).natDegree ≤ E) (r s : Index n W) (j : ℕ) :
    ((matrix (deformation p d) d W r s).coeff j).natDegree ≤ E := by
  rw [matrix_deformation_coefficient]
  split_ifs
  · exact polynomial_entry_degree_le p d W E hp r s
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · by_cases hrs : r = s <;> simp [Matrix.one_apply, hrs]
    · exact polynomial_entry_degree_le p d W E hp r s
  · simp

theorem det_polynomial_deformation_inner_degree {R : Type*} [CommRing R] {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i e, ((p i).coeff e).natDegree ≤ E) (j : ℕ) :
    ((matrix (deformation p d) d W).det.coeff j).natDegree ≤ FixedWidthPolynomial.count n W * E := by
  have h := PolynomialKronecker.determinant_inner_degree (matrix (deformation p d) d W) (fun _ => E)
    (polynomial_deformation_entry_inner_degree p d W E hp) j
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h

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
