/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CubePolynomial
public import LeanCanny.Algebra.MvCoefficientMass
import Mathlib.Tactic.Ring

/-! # Coefficient growth under rational compactification

Each cleared denominator factor has coefficient mass at most two. Its
exponent is at most twice the source degree in that coordinate. This bounds
the full compactified polynomial without expanding any denominator powers.
-/

@[expose] public section

namespace LeanCanny.Geometry.CubePolynomial
open MvPolynomial Algebra.MvMass
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem cleared_mass (p : MvPolynomial ι ℤ) :
    mass (cleared p) ≤ mass p * 2 ^ (2 * ∑ i, p.degreeOf i) := by
  classical
  apply (sum_le _ _).trans
  rw [mass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro e _
  apply (mul_le _ _).trans
  rw [C]
  apply Nat.mul_le_mul_left
  apply (prod_le _ _).trans
  have hden (i : ι) : mass (1 - (MvPolynomial.X i : MvPolynomial ι ℤ) ^ 2) ≤ 2 := by
    have hpow := pow_le (MvPolynomial.X i : MvPolynomial ι ℤ) 2
    have h := sub_le (1 : MvPolynomial ι ℤ) (MvPolynomial.X i ^ 2)
    simp only [one, X, one_pow] at hpow h
    omega
  calc
    (∏ i, mass ((MvPolynomial.X i : MvPolynomial ι ℤ) ^ e i * (1 - MvPolynomial.X i ^ 2) ^ (2 * p.degreeOf i - e i)))
        ≤ ∏ i, 2 ^ (2 * p.degreeOf i) := by
      apply Finset.prod_le_prod
      intro i _
      apply (mul_le _ _).trans
      have hX := pow_le (MvPolynomial.X i : MvPolynomial ι ℤ) (e i)
      have hD := (pow_le (1 - (MvPolynomial.X i : MvPolynomial ι ℤ) ^ 2) (2 * p.degreeOf i - e i)).trans
        (Nat.pow_le_pow_left (hden i) _)
      simp only [X, one_pow] at hX
      apply (Nat.mul_le_mul hX hD).trans
      rw [one_mul]
      exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]

theorem cleared_mass_of_degree (p : MvPolynomial ι ℤ) :
    mass (cleared p) ≤ mass p * 2 ^ (2 * Fintype.card ι * p.totalDegree) := by
  apply (cleared_mass p).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by decide)
  have h : (∑ i, p.degreeOf i) ≤ Fintype.card ι * p.totalDegree := by
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => degreeOf_le_totalDegree p i)
  exact (Nat.mul_le_mul_left 2 h).trans_eq (Nat.mul_assoc _ _ _).symm

end LeanCanny.Geometry.CubePolynomial
