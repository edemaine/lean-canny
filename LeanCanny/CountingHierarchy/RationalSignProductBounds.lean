/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RationalSignProduct

/-! # Explicit degree and log-mass bounds for the rational sign product -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped BigOperators Classical

theorem rationalSignProduct_natDegree_le (B s : ℕ) :
    (rationalSignProduct B s).natDegree ≤ 2 * s * (2 * B + 1) := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ Finset.range (2 * B + 1), 2 * s := by
      apply Finset.sum_le_sum
      intro j _
      apply Polynomial.natDegree_pow_le.trans
      conv_rhs => rw [← Nat.mul_one (2 * s)]
      apply Nat.mul_le_mul_left
      exact (Polynomial.natDegree_add_le _ _).trans (by
        apply max_le (by simp) _
        exact Polynomial.natDegree_mul_le.trans (by simp))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]; ring

theorem rationalSignProduct_mass_le (B s : ℕ) :
    coefficientMass (rationalSignProduct B s) ≤ 2 ^ (2 * s * (2 * B + 1) * (B + 1)) := by
  have hX : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
    change coefficientMass (Polynomial.monomial 1 (1 : ℤ)) = 1
    rw [coefficientMass_monomial]
    rfl
  have hlin (j : ℕ) (hj : j ∈ Finset.range (2 * B + 1)) :
      coefficientMass (Polynomial.C ((2 : ℤ) ^ (j - B)) +
        Polynomial.C ((2 : ℤ) ^ (B - j)) * Polynomial.X) ≤ 2 ^ (B + 1) := by
    apply (coefficientMass_add_le _ _).trans
    apply (Nat.add_le_add le_rfl (coefficientMass_mul_le _ _)).trans
    simp only [coefficientMass_C, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl,
      hX, Nat.mul_one]
    have hu : j - B ≤ B := by have := Finset.mem_range.mp hj; omega
    have hv : B - j ≤ B := Nat.sub_le _ _
    have ha := Nat.pow_le_pow_right (n := 2) (by decide) hu
    have hb := Nat.pow_le_pow_right (n := 2) (by decide) hv
    rw [pow_succ]
    omega
  apply (coefficientMass_prod_le _ _).trans
  calc
    _ ≤ ∏ _j ∈ Finset.range (2 * B + 1), (2 ^ (B + 1)) ^ (2 * s) := by
      apply Finset.prod_le_prod
      intro j hj
      exact (coefficientMass_pow_le _ _).trans (Nat.pow_le_pow_left (hlin j hj) _)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_range, ← pow_mul]
      congr 1
      ring

end LeanCanny.CountingHierarchy
