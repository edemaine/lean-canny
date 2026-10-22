/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientBounds

/-!
# Coefficient-mass bounds for polynomial arithmetic

The sum of absolute integer coefficients is subadditive and submultiplicative.
Finite sums, products, and powers inherit these bounds. These estimates permit
explicit bit budgets for rational substitution without expanding its terms.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial
open scoped BigOperators

theorem coefficientMass_add_le (p q : ℤ[X]) :
    coefficientMass (p + q) ≤ coefficientMass p + coefficientMass q := by
  let N := max p.natDegree q.natDegree + 1
  have hsum (u : ℤ[X]) (hu : u.natDegree < N) : coefficientMass u =
      ∑ i ∈ Finset.range N, (u.coeff i).natAbs :=
    u.sum_over_range' (fun _ => rfl) N hu
  have hp : p.natDegree < N := by dsimp [N]; omega
  have hq : q.natDegree < N := by dsimp [N]; omega
  have hpq : (p + q).natDegree < N := by
    have := Polynomial.natDegree_add_le p q
    dsimp [N]
    omega
  rw [hsum (p + q) hpq, hsum p hp, hsum q hq, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => by simpa only [Polynomial.coeff_add] using Int.natAbs_add_le (p.coeff i) (q.coeff i))

theorem coefficientMass_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    coefficientMass (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coefficientMass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (coefficientMass_add_le _ _).trans (Nat.add_le_add_left ih _)

@[simp] theorem coefficientMass_neg (p : ℤ[X]) : coefficientMass (-p) = coefficientMass p := by
  rw [coefficientMass, coefficientMass, Polynomial.sum_def, Polynomial.sum_def]
  simp only [Polynomial.support_neg, Polynomial.coeff_neg, Int.natAbs_neg]

theorem coefficientMass_sub_le (p q : ℤ[X]) :
    coefficientMass (p - q) ≤ coefficientMass p + coefficientMass q := by
  simpa only [sub_eq_add_neg, coefficientMass_neg] using coefficientMass_add_le p (-q)

@[simp] theorem coefficientMass_monomial (n : ℕ) (a : ℤ) : coefficientMass (monomial n a) = a.natAbs :=
  Polynomial.sum_monomial_index a _ rfl

theorem coefficientMass_mul_le (p q : ℤ[X]) :
    coefficientMass (p * q) ≤ coefficientMass p * coefficientMass q := by
  classical
  rw [Polynomial.mul_eq_sum_sum]
  simp only [Polynomial.sum_def]
  calc
    coefficientMass (∑ i ∈ p.support, ∑ j ∈ q.support, monomial (i + j) (p.coeff i * q.coeff j)) ≤
        ∑ i ∈ p.support, coefficientMass (∑ j ∈ q.support, monomial (i + j) (p.coeff i * q.coeff j)) :=
      coefficientMass_sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, coefficientMass (monomial (i + j) (p.coeff i * q.coeff j)) :=
      Finset.sum_le_sum (fun i _ => coefficientMass_sum_le _ _)
    _ = coefficientMass p * coefficientMass q := by
      simp only [coefficientMass_monomial, Int.natAbs_mul]
      rw [coefficientMass, coefficientMass, Polynomial.sum_def, Polynomial.sum_def, Finset.sum_mul]
      simp only [Finset.mul_sum]

theorem coefficientMass_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    coefficientMass (∏ i ∈ s, f i) ≤ ∏ i ∈ s, coefficientMass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, ← Polynomial.C_1, coefficientMass_C]; decide
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (coefficientMass_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem coefficientMass_pow_le (p : ℤ[X]) (n : ℕ) : coefficientMass (p ^ n) ≤ coefficientMass p ^ n := by
  induction n with
  | zero => simp only [pow_zero, ← Polynomial.C_1, coefficientMass_C]; decide
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (coefficientMass_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

theorem coefficientMass_le_pow_of_degree_coeff (p : ℤ[X]) (D b : ℕ)
    (hD : p.natDegree ≤ D) (hb : ∀ k, (p.coeff k).natAbs ≤ 2 ^ b) :
    coefficientMass p ≤ 2 ^ (b + (D + 1).size) := by
  calc
    _ ≤ (D + 1) * 2 ^ b := coefficientMass_le p D _ hD hb
    _ ≤ 2 ^ (D + 1).size * 2 ^ b := Nat.mul_le_mul_right _ (Nat.lt_size_self (D + 1)).le
    _ = _ := by rw [← pow_add, Nat.add_comm]

end LeanCanny.Algebra
