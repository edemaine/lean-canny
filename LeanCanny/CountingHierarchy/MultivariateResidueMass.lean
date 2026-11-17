/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.MultivariateParameterMass
public import LeanCanny.CountingHierarchy.ResidueMassBounds
public import LeanCanny.CountingHierarchy.PurePowerResidue
public import Mathlib.Data.Fintype.BigOperators

/-! # Finite residue mass over multivariate parameter rings -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial LeanCanny.Algebra
open scoped BigOperators Classical

variable {τ : Type*}

namespace MultivariateParameterMass

/-- Leibniz expansion bounds a polynomial-parameter determinant without
 requiring a matrix algorithm. -/
theorem det_le {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ (MvPolynomial τ ℤ))) (M : ℕ)
    (hM : ∀ i j, mass (A i j) ≤ M) :
    mass A.det ≤ (Fintype.card ι).factorial * M ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  apply (sum_le _ _).trans
  have hu (u : ℤˣ) (p : MvPolynomial σ (MvPolynomial τ ℤ)) : mass (u • p) = mass p := by
    rcases Int.units_eq_one_or u with h | h <;> simp [h, Units.smul_def]
  calc
    _ ≤ ∑ _π : Equiv.Perm ι, ∏ _j : ι, M := by
      apply Finset.sum_le_sum
      intro π _
      rw [hu]
      exact (prod_le _ _).trans (Finset.prod_le_prod fun j _ => hM (π j) j)
    _ = _ := by simp [Fintype.card_perm]

end MultivariateParameterMass

namespace PurePowerResidue.MultivariateParameters

/-- A rectangular truncation has a direct mass bound from its displayed
 coefficient formula. All powers and the term count have short exponents. -/
theorem truncated_mass_le {n : ℕ} (ell B R : ℕ) (hR : 1 ≤ R)
    (r : Fin n → MvPolynomial (Fin n) (MvPolynomial τ ℤ))
    (hr : ∀ i, MultivariateParameterMass.mass (r i) ≤ R)
    (v : MvPolynomial (Fin n) (MvPolynomial τ ℤ)) :
    MvMass.mass (truncated ell r B v) ≤
      (B + 1) ^ n * (MultivariateParameterMass.mass v * (R ^ B) ^ n) := by
  change MvMass.mass (∑ j ∈ indices n B, term ell r v j) ≤ _
  apply (MvMass.sum_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ indices n B, MultivariateParameterMass.mass v * (R ^ B) ^ n := by
      apply Finset.sum_le_sum
      intro j hj
      apply (MultivariateParameterMass.coeff_le (v * ∏ i, r i ^ j i) (target ell j)).trans
      apply (MultivariateParameterMass.mul_le _ _).trans
      apply Nat.mul_le_mul_left
      apply (MultivariateParameterMass.prod_le _ _).trans
      calc
        _ ≤ ∏ _i : Fin n, R ^ B := by
          apply Finset.prod_le_prod
          intro i _
          exact (MultivariateParameterMass.pow_le _ _).trans
            ((Nat.pow_le_pow_left (hr i) _).trans
              (Nat.pow_le_pow_right hR (mem_indices.mp hj i)))
        _ = _ := by simp
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, card_indices, Nat.cast_id]

theorem residue_mass_le {n ell : ℕ} (hell : 1 ≤ ell) (B R : ℕ) (hR : 1 ≤ R)
    (r : Fin n → MvPolynomial (Fin n) (MvPolynomial τ ℤ))
    (hr : ∀ i, (r i).totalDegree < ell) (hM : ∀ i, MultivariateParameterMass.mass (r i) ≤ R)
    (v : MvPolynomial (Fin n) (MvPolynomial τ ℤ)) (hB : v.totalDegree ≤ B) :
    MvMass.mass (residue ell r v) ≤
      (B + 1) ^ n * (MultivariateParameterMass.mass v * (R ^ B) ^ n) := by
  rw [residue_eq_truncated hell r hr v hB]
  exact truncated_mass_le ell B R hR r hM v

end PurePowerResidue.MultivariateParameters
end LeanCanny.CountingHierarchy
