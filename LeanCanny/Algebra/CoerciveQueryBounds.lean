/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoerciveQuerySystem
public import LeanCanny.Algebra.CoerciveRadiusBits

/-! # A common coefficient budget for the actual coercive sample queries -/

@[expose] public section
namespace LeanCanny.Algebra.CoerciveQuerySystem
open scoped Classical

variable {n : ℕ}

def height (n D b E : ℕ) : ℕ := E + (D.size + 2 * b + 3) + n.size + 1

private theorem sum_powers_le (a b : ℕ) : 2 ^ a + 2 ^ b ≤ 2 ^ (a + b + 1) := by
  have h1 : 2 ^ a ≤ 2 ^ (a + b) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ b ≤ 2 ^ (a + b) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ]
  omega

theorem gradient_mass_le_pow (q : MvPolynomial (Fin n) ℤ) (D b E : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) (i : Fin n) :
    MvMass.mass (gradient q D i) ≤ 2 ^ height n D b E := by
  apply (gradient_mass q D hD i).trans
  have hbudget := CoerciveRadiusBits.coefficientBudget_le q D b hb
  have hsmall : 2 * D * MvMass.mass q ^ 2 + (2 * D + 2) ≤
      CoerciveCriticalBounds.coefficientBudget q D := by
    unfold CoerciveCriticalBounds.coefficientBudget
    nlinarith
  exact (hsmall.trans hbudget).trans (Nat.pow_le_pow_right (by decide) (by
    unfold CoerciveRadiusBits.budgetExponent height
    omega))

theorem residual_mass_le_pow (q : MvPolynomial (Fin n) ℤ) (D b E : ℕ)
    (hb : MvMass.mass q ≤ 2 ^ b) :
    MvMass.mass (residual q E) ≤ 2 ^ height n D b E := by
  have hq : MvMass.mass q ^ 2 ≤ 2 ^ (2 * b) := by
    simpa only [← pow_mul, Nat.mul_comm b 2] using Nat.pow_le_pow_left hb 2
  exact (residual_mass q E).trans ((Nat.add_le_add_right hq _).trans
    ((sum_powers_le (2 * b) E).trans (Nat.pow_le_pow_right (by decide) (by unfold height; omega))))

theorem bound_mass_le_pow (D b E : ℕ) :
    MvMass.mass (bound (n := n) D E) ≤ 2 ^ height n D b E :=
  (bound_mass D E).trans ((Nat.add_le_add_right (Nat.lt_size_self n).le _).trans
    ((sum_powers_le n.size E).trans (Nat.pow_le_pow_right (by decide) (by unfold height; omega))))

end LeanCanny.Algebra.CoerciveQuerySystem
