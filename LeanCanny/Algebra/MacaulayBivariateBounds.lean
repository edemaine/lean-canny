/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayBounds
public import LeanCanny.Algebra.PolynomialKronecker

/-! # Integer coefficient bounds for bivariate Macaulay determinants

A radix above the determinant's full inner degree preserves each selected
coefficient. Bounds for the encoded input coefficient masses then give the
usual determinant bit allowance, including requests above the inner degree.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical

theorem matrix_inner_degree {R : Type*} [CommRing R] {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) (Polynomial (Polynomial R))) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i e j, (((p i).coeff e).coeff j).natDegree ≤ E) (r s : Index n W) (j : ℕ) :
    (((matrix p d W r s).coeff j).natDegree) ≤ E := by
  by_cases hr : (FixedWidthPolynomial.vector n W r).degree = level d
  · rw [entry_active p d W r s hr]
    split_ifs
    · exact hp _ _ j
    · simp
  · simp only [matrix, dite_eq_right hr]
    change ((if r = s then (1 : Polynomial (Polynomial R)) else 0).coeff j).natDegree ≤ E
    by_cases hrs : r = s <;> by_cases hj : j = 0 <;> simp [hrs, hj, Polynomial.coeff_one]

theorem det_inner_degree {R : Type*} [CommRing R] {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) (Polynomial (Polynomial R))) (d : Fin n → ℕ) (W E : ℕ)
    (hp : ∀ i e j, (((p i).coeff e).coeff j).natDegree ≤ E) (j : ℕ) :
    (((matrix p d W).det.coeff j).natDegree) ≤ FixedWidthPolynomial.count n W * E := by
  have h := PolynomialKronecker.determinant_inner_degree (matrix p d W) (fun _ => E) (matrix_inner_degree p d W E hp) j
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h

theorem det_bivariate_coefficient_size_le {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) (Polynomial (Polynomial ℤ))) (d : Fin n → ℕ) (W E b : ℕ)
    (hdeg : ∀ i e j, (((p i).coeff e).coeff j).natDegree ≤ E)
    (hmass : ∀ B i e, coefficientMass (PolynomialKronecker.encode B ((p i).coeff e)) ≤ 2 ^ b) (k l : ℕ) :
    ((((matrix p d W).det.coeff l).coeff k).natAbs.size) ≤
      (FixedWidthPolynomial.count n W).size * FixedWidthPolynomial.count n W + FixedWidthPolynomial.count n W * b + 1 := by
  let B := FixedWidthPolynomial.count n W * E + 1
  by_cases hk : k < B
  · have hc := PolynomialKronecker.coefficient B (matrix p d W).det
      (fun j => (det_inner_degree p d W E hdeg j).trans_lt (Nat.lt_succ_self _)) k l hk
    have hm : PolynomialKronecker.encode B (matrix p d W).det =
        (matrix (fun i => (p i).map (PolynomialKronecker.encode B)) d W).det := by
      have hmap : PolynomialKronecker.encode B (matrix p d W).det = ((matrix p d W).map (PolynomialKronecker.encode B)).det :=
        (PolynomialKronecker.encode B).map_det _
      rw [matrix_map] at hmap
      exact hmap
    rw [hm] at hc
    rw [← hc]
    apply det_coefficient_size_le _ d W b
    intro i e
    rw [MvPolynomial.coeff_map]
    exact hmass B i e
  · have hz : ((matrix p d W).det.coeff l).coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hd := det_inner_degree p d W E hdeg l
      dsimp only [B] at hk
      omega
    rw [hz]
    simp

end LeanCanny.Algebra.Macaulay
