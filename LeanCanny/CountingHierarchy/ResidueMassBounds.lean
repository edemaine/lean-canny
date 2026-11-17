/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParameterMass
public import LeanCanny.CountingHierarchy.PurePowerResidue
public import Mathlib.Data.Fintype.BigOperators

/-! # Coefficient-mass bounds for parameter-valued finite residues -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial LeanCanny.Algebra
open scoped BigOperators Classical

namespace ParameterMass

/-- Leibniz expansion bounds a polynomial-parameter determinant without
 requiring a matrix algorithm. -/
theorem det_le {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ (Polynomial ℤ))) (M : ℕ)
    (hM : ∀ i j, mass (A i j) ≤ M) :
    mass A.det ≤ (Fintype.card ι).factorial * M ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  apply (sum_le _ _).trans
  have hu (u : ℤˣ) (p : MvPolynomial σ (Polynomial ℤ)) : mass (u • p) = mass p := by
    rcases Int.units_eq_one_or u with h | h <;> simp [h, Units.smul_def]
  calc
    _ ≤ ∑ _π : Equiv.Perm ι, ∏ _j : ι, M := by
      apply Finset.sum_le_sum
      intro π _
      rw [hu]
      exact (prod_le _ _).trans (Finset.prod_le_prod fun j _ => hM (π j) j)
    _ = _ := by simp [Fintype.card_perm]

end ParameterMass

namespace PurePowerResidue

@[simp] theorem card_indices (n B : ℕ) : (indices n B).card = (B + 1) ^ n := by
  simp only [indices, Fintype.card_piFinset, Finset.card_range, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- A rectangular truncation has a direct mass bound from its displayed
 coefficient formula. All powers and the term count have short exponents. -/
theorem truncated_coefficientMass_le {n : ℕ} (ell B R : ℕ) (hR : 1 ≤ R)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, ParameterMass.mass (r i) ≤ R)
    (v : MvPolynomial (Fin n) (Polynomial ℤ)) :
    coefficientMass (truncated ell r B v) ≤
      (B + 1) ^ n * (ParameterMass.mass v * (R ^ B) ^ n) := by
  change coefficientMass (∑ j ∈ indices n B, term ell r v j) ≤ _
  apply (coefficientMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ indices n B, ParameterMass.mass v * (R ^ B) ^ n := by
      apply Finset.sum_le_sum
      intro j hj
      apply (ParameterMass.coeff_le (v * ∏ i, r i ^ j i) (target ell j)).trans
      apply (ParameterMass.mul_le _ _).trans
      apply Nat.mul_le_mul_left
      apply (ParameterMass.prod_le _ _).trans
      calc
        _ ≤ ∏ _i : Fin n, R ^ B := by
          apply Finset.prod_le_prod
          intro i _
          exact (ParameterMass.pow_le _ _).trans
            ((Nat.pow_le_pow_left (hr i) _).trans
              (Nat.pow_le_pow_right hR (mem_indices.mp hj i)))
        _ = _ := by simp
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, card_indices, Nat.cast_id]

theorem residue_coefficientMass_le {n ell : ℕ} (hell : 1 ≤ ell) (B R : ℕ) (hR : 1 ≤ R)
    (r : Fin n → MvPolynomial (Fin n) (Polynomial ℤ))
    (hr : ∀ i, (r i).totalDegree < ell) (hM : ∀ i, ParameterMass.mass (r i) ≤ R)
    (v : MvPolynomial (Fin n) (Polynomial ℤ)) (hB : v.totalDegree ≤ B) :
    coefficientMass (residue ell r v) ≤
      (B + 1) ^ n * (ParameterMass.mass v * (R ^ B) ^ n) := by
  rw [residue_eq_truncated hell r hr v hB]
  exact truncated_coefficientMass_le ell B R hR r hM v

end PurePowerResidue
end LeanCanny.CountingHierarchy
