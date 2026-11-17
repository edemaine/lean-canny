/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientMass

/-! # Coefficient-mass bounds for integer polynomial composition -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped BigOperators Classical

theorem coefficientMass_comp_le (p q : Polynomial ℤ) (D M : ℕ)
    (hD : p.natDegree ≤ D) (hM : 1 ≤ M) (hq : coefficientMass q ≤ M) :
    coefficientMass (p.comp q) ≤ coefficientMass p * M ^ D := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def]
  apply (coefficientMass_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ p.support, (p.coeff i).natAbs * M ^ D := by
      apply Finset.sum_le_sum
      intro i hi
      apply (coefficientMass_mul_le _ _).trans
      rw [coefficientMass_C]
      apply Nat.mul_le_mul_left
      exact (coefficientMass_pow_le _ _).trans
        ((Nat.pow_le_pow_left hq i).trans
          (Nat.pow_le_pow_right hM ((Polynomial.le_natDegree_of_mem_supp i hi).trans hD)))
    _ = _ := by rw [coefficientMass, Polynomial.sum_def, Finset.sum_mul]

/-- Log-mass budgets compose by one multiplication and addition. -/
theorem coefficientMass_comp_le_pow (p q : Polynomial ℤ) (D bp bq : ℕ)
    (hD : p.natDegree ≤ D) (hp : coefficientMass p ≤ 2 ^ bp) (hq : coefficientMass q ≤ 2 ^ bq) :
    coefficientMass (p.comp q) ≤ 2 ^ (bp + D * bq) := by
  apply (coefficientMass_comp_le p q D (2 ^ bq) hD Nat.one_le_two_pow hq).trans
  exact (Nat.mul_le_mul_right _ hp).trans_eq (by rw [← pow_mul, ← pow_add, Nat.mul_comm D])

end LeanCanny.CountingHierarchy
