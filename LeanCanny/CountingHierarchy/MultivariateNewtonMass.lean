/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CharacteristicNewton
public import LeanCanny.CountingHierarchy.PolynomialParameterMass

/-! # Multivariate-parameter characteristic bounds from power traces

Newton's integer multiplier cancels the number of summands. This bounds
characteristic coefficients without computing or bounding quotient matrix entries.
-/

public section

namespace LeanCanny.CountingHierarchy.MultivariateNewtonMass

open Polynomial LeanCanny.Algebra
open scoped BigOperators Classical

variable {τ : Type*}

/-- The mass analogue of Newton recurrence over the multivariate integer parameter ring. -/
theorem newton_coefficient_mass_le (D A : ℕ) (c t : ℕ → MvPolynomial τ ℤ)
    (hzero : c 0 = 1)
    (hrec : ∀ k < D, (k + 1) • c (k + 1) =
      -(∑ j ∈ Finset.range (k + 1), c (k - j) * t (j + 1)))
    (ht : ∀ j, 1 ≤ j → j ≤ D → MvMass.mass (t j) ≤ A ^ j)
    (k : ℕ) (hk : k ≤ D) : MvMass.mass (c k) ≤ A ^ k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    cases k with
    | zero => simp only [hzero, pow_zero, ← MvPolynomial.C_1, MvMass.C, Int.natAbs_one, le_refl]
    | succ k =>
      have hb : (k + 1) * MvMass.mass (c (k + 1)) ≤ (k + 1) * A ^ (k + 1) := by
        calc
          _ = MvMass.mass ((k + 1) • c (k + 1)) := (MvMass.mass_nsmul _ _).symm
          _ = MvMass.mass (-(∑ j ∈ Finset.range (k + 1), c (k - j) * t (j + 1))) :=
            congrArg MvMass.mass (hrec k (by omega))
          _ ≤ ∑ j ∈ Finset.range (k + 1), MvMass.mass (c (k - j) * t (j + 1)) := by
            rw [MvMass.neg]
            exact MvMass.sum_le _ _
          _ ≤ ∑ _j ∈ Finset.range (k + 1), A ^ (k + 1) := by
            apply Finset.sum_le_sum
            intro j hj
            have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
            apply (MvMass.mul_le _ _).trans
            have hc := ih (k - j) (by omega) (by omega)
            exact (Nat.mul_le_mul hc (ht (j + 1) (by omega) (by omega))).trans_eq
              (by rw [← pow_add]; congr 1; omega)
          _ = _ := by simp
      exact Nat.le_of_mul_le_mul_left hb (by omega)

/-- Polynomial-valued matrices inherit the coefficient bound from bounds
 on the masses of their power traces. -/
theorem charpolyRev_coefficient_mass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial τ ℤ)) (A : ℕ)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → MvMass.mass ((M ^ j).trace) ≤ A ^ j)
    (k : ℕ) (hk : k ≤ Fintype.card ι) :
    MvMass.mass (M.charpolyRev.coeff k) ≤ A ^ k := by
  apply newton_coefficient_mass_le (Fintype.card ι) A
    (fun j => M.charpolyRev.coeff j) (fun j => (M ^ j).trace) _ _ ht k hk
  · rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  · intro j _
    simpa only [nsmul_eq_mul] using charpolyRev_newton M j

/-- A uniform power-trace mass exponent bounds every characteristic coefficient. -/
theorem charpoly_coefficient_mass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial τ ℤ)) (b : ℕ)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → MvMass.mass ((M ^ j).trace) ≤ 2 ^ b)
    (k : ℕ) : MvMass.mass (M.charpoly.coeff k) ≤ 2 ^ (b * Fintype.card ι) := by
  by_cases hk : k ≤ Fintype.card ι
  · have hrev := charpolyRev_coefficient_mass_le M (2 ^ b) (by
      intro j hj hle
      exact (ht j hj hle).trans (by
        simpa only [pow_one] using Nat.pow_le_pow_right (Nat.one_le_two_pow) hj))
      (Fintype.card ι - k) (Nat.sub_le _ _)
    rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse,
      Matrix.charpoly_natDegree_eq_dim, Polynomial.revAt_le (Nat.sub_le _ _),
      Nat.sub_sub_self hk] at hrev
    apply hrev.trans
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left b (Nat.sub_le _ _))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim]; omega),
      MvMass.zero]
    exact Nat.zero_le _

/-- Total integer mass of the multivariate-parameter characteristic polynomial. -/
theorem charpoly_nestedMass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial τ ℤ)) (b : ℕ)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → MvMass.mass ((M ^ j).trace) ≤ 2 ^ b) :
    PolynomialParameterMass.mass M.charpoly ≤
      2 ^ (b * Fintype.card ι + (Fintype.card ι + 1).size) :=
  PolynomialParameterMass.le_pow M.charpoly (Fintype.card ι) (b * Fintype.card ι)
    (by rw [Matrix.charpoly_natDegree_eq_dim]) (charpoly_coefficient_mass_le M b ht)

end LeanCanny.CountingHierarchy.MultivariateNewtonMass
