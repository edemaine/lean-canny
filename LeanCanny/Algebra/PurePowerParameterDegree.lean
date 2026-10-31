/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PurePowerRelativeAnnihilator
public import LeanCanny.Algebra.PolynomialCoefficientDegree
public import LeanCanny.Algebra.RelativeMatrixDegree

/-! # Relative parameter degrees of constructed coordinate annihilators

If every lower relation coefficient has parameter degree at most E, the
constructed coordinate annihilator has coefficient degrees at most
N*(bound+1)*E, where N is the explicit fixed-width spatial state count.
The common leading coefficient is constant in the retained parameter.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerParameterDegree
open PurePowerReductionMatrix
open scoped Classical
variable {n B : ℕ} {R : Type*} [CommRing R]

theorem step (low : MvPolynomial (Fin n) (Polynomial R)) (E : ℕ)
    (hlow : PolynomialCoefficientDegree.Bound low E) (e m : Fin n →₀ ℕ) (r : Fin n) (d : ℕ) :
    ((MonicMonomialReduction.step low e r d).coeff m).natDegree ≤ E := by
  rw [MonicMonomialReduction.step_coefficient]
  split_ifs
  · simpa only [Polynomial.natDegree_neg] using hlow _
  · simp

theorem matrix (fallback : Fin n) (d : Fin n → ℕ) (low : Fin n → MvPolynomial (Fin n) (Polynomial R))
    (E : ℕ) (hlow : ∀ i, PolynomialCoefficientDegree.Bound (low i) E) (c : Polynomial R)
    (hc : c.natDegree ≤ E) (bound : ℕ) :
    RelativeMatrixDegree.Bound (PurePowerReductionMatrix.matrix (B := B) fallback d low c bound) E := by
  intro i j
  by_cases hn : Normal d (FixedWidthPolynomial.vector n B j)
  · rw [normal_column fallback d low c bound j hn i]
    split_ifs
    · exact hc
    · simp
  · by_cases hv : (FixedWidthPolynomial.vector n B j).degree ≤ bound
    · rw [PurePowerReductionMatrix.matrix, ite_eq_right hn, ite_eq_left hv]
      exact step _ E (hlow _) _ _ _ _
    · simp only [PurePowerReductionMatrix.matrix, ite_eq_right hn, ite_eq_right hv, Polynomial.natDegree_zero,
        Nat.zero_le]

theorem actionMatrix (fallback : Fin n) (d : Fin n → ℕ) (low : Fin n → MvPolynomial (Fin n) (Polynomial R))
    (E : ℕ) (hlow : ∀ i, PolynomialCoefficientDegree.Bound (low i) E) (c : Polynomial R)
    (hc : c.natDegree ≤ E) (bound : ℕ) (hgrid : gridBound d + 1 ≤ bound) (hbound : bound < 2 ^ B)
    (r : Fin n) :
    RelativeMatrixDegree.Bound (PurePowerRelativeAnnihilator.actionMatrix fallback d low c bound hgrid hbound r)
      ((bound + 1) * E) := by
  have HP := RelativeMatrixDegree.pow (matrix (B := B) fallback d low E hlow c hc bound) (bound + 1)
  intro i j
  unfold PurePowerRelativeAnnihilator.actionMatrix GradedReductionAnnihilator.paddedMatrix
  split_ifs
  · exact HP i _
  · simp

theorem coefficient (fallback : Fin n) (d : Fin n → ℕ) (low : Fin n → MvPolynomial (Fin n) (Polynomial R))
    (E : ℕ) (hlow : ∀ i, PolynomialCoefficientDegree.Bound (low i) E) (a : R) (bound : ℕ)
    (hgrid : gridBound d + 1 ≤ bound) (hbound : bound < 2 ^ B) (r : Fin n) (k : ℕ) :
    ((PurePowerRelativeAnnihilator.polynomial fallback d low (Polynomial.C a) bound hgrid hbound r).coeff k).natDegree ≤
      FixedWidthPolynomial.count n B * ((bound + 1) * E) := by
  rw [PurePowerRelativeAnnihilator.polynomial, ScaledGradedReductionAnnihilator.coefficient, ← Polynomial.C_pow]
  apply Polynomial.natDegree_mul_le.trans
  rw [Polynomial.natDegree_C, Nat.add_zero]
  simpa only [Fintype.card_fin] using RelativeMatrixDegree.charpoly_coefficient
    (actionMatrix fallback d low E hlow (Polynomial.C a) (by simp) bound hgrid hbound r) k

end LeanCanny.Algebra.PurePowerParameterDegree
