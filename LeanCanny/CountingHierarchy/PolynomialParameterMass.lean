/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.MvMassNsmul
public import Mathlib.Data.Nat.Size
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-! # Polynomial mass over multivariate integer parameters

Summing multivariate coefficient masses retains subadditivity and
submultiplicativity before specializing any retained parameters.
-/

@[expose] public section

namespace LeanCanny.CountingHierarchy.PolynomialParameterMass
open Polynomial LeanCanny.Algebra
open scoped BigOperators

variable {τ : Type*}

noncomputable def mass (p : Polynomial (MvPolynomial τ ℤ)) : ℕ := p.sum fun _ a => MvMass.mass a

@[simp] theorem zero : mass (0 : Polynomial (MvPolynomial τ ℤ)) = 0 := by simp [mass]
@[simp] theorem C (a : MvPolynomial τ ℤ) : mass (Polynomial.C a) = MvMass.mass a := by simp [mass]
@[simp] theorem monomial (i : ℕ) (a : MvPolynomial τ ℤ) : mass (Polynomial.monomial i a) = MvMass.mass a :=
  Polynomial.sum_monomial_index a _ MvMass.zero

theorem range_sum (p : Polynomial (MvPolynomial τ ℤ)) (N : ℕ) (hN : p.natDegree < N) :
    mass p = ∑ i ∈ Finset.range N, MvMass.mass (p.coeff i) :=
  p.sum_over_range' (fun _ => MvMass.zero) N hN

theorem coeff_le (p : Polynomial (MvPolynomial τ ℤ)) (i : ℕ) : MvMass.mass (p.coeff i) ≤ mass p := by
  classical
  by_cases hi : i ∈ p.support
  · change MvMass.mass (p.coeff i) ≤ ∑ j ∈ p.support, MvMass.mass (p.coeff j)
    exact Finset.single_le_sum (f := fun j => MvMass.mass (p.coeff j)) (fun _ _ => Nat.zero_le _) hi
  · rw [Polynomial.notMem_support_iff.mp hi, MvMass.zero]
    exact Nat.zero_le _

theorem le_degree_coeff (p : Polynomial (MvPolynomial τ ℤ)) (D H : ℕ) (hD : p.natDegree ≤ D)
    (hH : ∀ i, MvMass.mass (p.coeff i) ≤ H) : mass p ≤ (D + 1) * H := by
  rw [range_sum p (D + 1) (by omega)]
  exact (Finset.sum_le_sum (fun i _ => hH i)).trans_eq (by simp)

theorem le_pow (p : Polynomial (MvPolynomial τ ℤ)) (D b : ℕ) (hD : p.natDegree ≤ D)
    (hb : ∀ i, MvMass.mass (p.coeff i) ≤ 2 ^ b) : mass p ≤ 2 ^ (b + (D + 1).size) := by
  calc
    _ ≤ (D + 1) * 2 ^ b := le_degree_coeff p D _ hD hb
    _ ≤ 2 ^ (D + 1).size * 2 ^ b := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _ = _ := by rw [← pow_add, Nat.add_comm]

theorem add_le (p q : Polynomial (MvPolynomial τ ℤ)) : mass (p + q) ≤ mass p + mass q := by
  let N := max p.natDegree q.natDegree + 1
  have hp : p.natDegree < N := by dsimp [N]; omega
  have hq : q.natDegree < N := by dsimp [N]; omega
  have hs : (p + q).natDegree < N := (natDegree_add_le p q).trans_lt (by dsimp [N]; omega)
  rw [range_sum (p + q) N hs, range_sum p N hp, range_sum q N hq, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by simpa only [coeff_add] using MvMass.add_le (p.coeff i) (q.coeff i)

@[simp] theorem neg (p : Polynomial (MvPolynomial τ ℤ)) : mass (-p) = mass p := by
  rw [mass, mass, Polynomial.sum_def, Polynomial.sum_def]
  simp only [Polynomial.support_neg, Polynomial.coeff_neg, MvMass.neg]

theorem sub_le (p q : Polynomial (MvPolynomial τ ℤ)) : mass (p - q) ≤ mass p + mass q := by
  simpa only [sub_eq_add_neg, neg] using add_le p (-q)

theorem sum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial (MvPolynomial τ ℤ)) : mass (∑ i ∈ s, f i) ≤ ∑ i ∈ s, mass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (add_le _ _).trans (Nat.add_le_add_left ih _)

theorem mul_le (p q : Polynomial (MvPolynomial τ ℤ)) : mass (p * q) ≤ mass p * mass q := by
  classical
  rw [Polynomial.mul_eq_sum_sum]
  simp only [Polynomial.sum_def]
  calc
    _ ≤ ∑ i ∈ p.support, mass (∑ j ∈ q.support, Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) := sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, mass (Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) :=
      Finset.sum_le_sum fun i _ => sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, MvMass.mass (p.coeff i) * MvMass.mass (q.coeff j) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun j _ => by simpa only [monomial] using MvMass.mul_le (p.coeff i) (q.coeff j)
    _ = _ := by
      rw [mass, mass, Polynomial.sum_def, Polynomial.sum_def, Finset.sum_mul]
      simp only [Finset.mul_sum]

theorem prod_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial (MvPolynomial τ ℤ)) : mass (∏ i ∈ s, f i) ≤ ∏ i ∈ s, mass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, ← Polynomial.C_1, C, MvMass.one]; decide
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem pow_le (p : Polynomial (MvPolynomial τ ℤ)) (n : ℕ) : mass (p ^ n) ≤ mass p ^ n := by
  induction n with
  | zero => simp only [pow_zero, ← Polynomial.C_1, C, MvMass.one]; decide
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

end LeanCanny.CountingHierarchy.PolynomialParameterMass
