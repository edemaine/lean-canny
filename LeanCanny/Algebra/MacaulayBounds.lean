/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayDeformation

/-! # Size bounds for the padded Macaulay determinant

Entry access selects an input coefficient or an identity entry. Consequently the
existing determinant estimates apply without summing all input monomials.
For integer inputs the linear deformation increases the coefficient-mass budget
by at most two bits. These are algebraic bounds, not complexity certificates.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay

variable {n : ℕ}

theorem matrix_entry_mass_le (p : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (d : Fin n → ℕ) (W B : ℕ)
    (hp : ∀ i e, coefficientMass ((p i).coeff e) ≤ 2 ^ B) (r s : Index n W) :
    coefficientMass (matrix p d W r s) ≤ 2 ^ B := by
  by_cases hr : (FixedWidthPolynomial.vector n W r).degree = level d
  · rw [entry_active p d W r s hr]
    split_ifs
    · exact hp _ _
    · simp
  · simp only [matrix, dite_eq_right hr, Matrix.one_apply]
    split_ifs
    · change coefficientMass (Polynomial.C (1 : ℤ)) ≤ 2 ^ B
      rw [coefficientMass_C]
      exact Nat.one_le_two_pow
    · simp

theorem det_coefficient_size_le (p : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (d : Fin n → ℕ) (W B : ℕ)
    (hp : ∀ i e, coefficientMass ((p i).coeff e) ≤ 2 ^ B) (k : ℕ) :
    ((matrix p d W).det.coeff k).natAbs.size ≤
      (FixedWidthPolynomial.count n W).size * FixedWidthPolynomial.count n W +
        FixedWidthPolynomial.count n W * B + 1 := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
    det_coeff_size_le (matrix p d W) (fun _ => B)
      (fun r s => matrix_entry_mass_le p d W B hp r s) k

theorem coefficient_deformation_mass_le (p : Fin n → MvPolynomial (Fin n) ℤ)
    (d : Fin n → ℕ) (B : ℕ) (hp : ∀ i e, ((p i).coeff e).natAbs ≤ 2 ^ B)
    (i : Fin n) (e : Fin n →₀ ℕ) :
    coefficientMass ((deformation p d i).coeff e) ≤ 2 ^ (B + 2) := by
  have hdeg := coefficient_deformation_degree_le p d i e
  have hc : ∀ k, (((deformation p d i).coeff e).coeff k).natAbs ≤ 2 ^ B + 1 := by
    intro k
    by_cases hk0 : k = 0
    · simpa [coefficient_deformation, hk0] using (hp i e).trans (Nat.le_add_right _ _)
    by_cases hk1 : k = 1
    · subst k
      have hdelta : ((if Finsupp.single i (d i) = e then 1 else 0) : ℤ).natAbs ≤ 1 := by
        split_ifs <;> decide
      have h := (Int.natAbs_sub_le (if Finsupp.single i (d i) = e then 1 else 0)
        ((p i).coeff e)).trans (Nat.add_le_add hdelta (hp i e))
      rw [coefficient_deformation]
      simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_sub,
        Polynomial.coeff_C, Nat.one_ne_zero, ite_false, zero_add]
      split_ifs at h ⊢ <;> simpa [Nat.add_comm] using h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (by omega))]
      exact Nat.zero_le _
  have h := coefficientMass_le ((deformation p d i).coeff e) 1 (2 ^ B + 1) hdeg hc
  apply h.trans
  have hpos := (Nat.one_le_two_pow (n := B))
  calc
    (1 + 1) * (2 ^ B + 1) ≤ 4 * 2 ^ B := by omega
    _ = 2 ^ (B + 2) := by rw [pow_add]; ring

theorem det_deformation_coefficient_size_le (p : Fin n → MvPolynomial (Fin n) ℤ)
    (d : Fin n → ℕ) (W B : ℕ) (hp : ∀ i e, ((p i).coeff e).natAbs ≤ 2 ^ B) (k : ℕ) :
    ((matrix (deformation p d) d W).det.coeff k).natAbs.size ≤
      (FixedWidthPolynomial.count n W).size * FixedWidthPolynomial.count n W +
        FixedWidthPolynomial.count n W * (B + 2) + 1 :=
  det_coefficient_size_le (deformation p d) d W (B + 2)
    (coefficient_deformation_mass_le p d B hp) k

end LeanCanny.Algebra.Macaulay
