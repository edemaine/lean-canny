/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientMass
public import LeanCanny.Algebra.PseudoRemainder
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-! # Total coefficient mass for integer bivariate polynomials

Summing the inner coefficient masses gives the same subadditive and
submultiplicative bounds as in one variable. In particular, pseudo-reduction
can be bounded over the polynomial parameter ring before specializing beta.
-/

@[expose] public section

namespace LeanCanny.Algebra.NestedMass
open Polynomial
open scoped BigOperators

noncomputable def mass (p : (ℤ[X])[X]) : ℕ := p.sum fun _ a => coefficientMass a

@[simp] theorem zero : mass 0 = 0 := by simp [mass]
@[simp] theorem C (a : ℤ[X]) : mass (Polynomial.C a) = coefficientMass a := by simp [mass]
@[simp] theorem monomial (i : ℕ) (a : ℤ[X]) : mass (Polynomial.monomial i a) = coefficientMass a :=
  Polynomial.sum_monomial_index a _ coefficientMass_zero

theorem range_sum (p : (ℤ[X])[X]) (N : ℕ) (hN : p.natDegree < N) :
    mass p = ∑ i ∈ Finset.range N, coefficientMass (p.coeff i) :=
  p.sum_over_range' (fun _ => coefficientMass_zero) N hN

theorem coeff_le (p : (ℤ[X])[X]) (i : ℕ) : coefficientMass (p.coeff i) ≤ mass p := by
  classical
  by_cases hi : i ∈ p.support
  · change coefficientMass (p.coeff i) ≤ ∑ j ∈ p.support, coefficientMass (p.coeff j)
    exact Finset.single_le_sum (f := fun j => coefficientMass (p.coeff j)) (fun _ _ => Nat.zero_le _) hi
  · rw [Polynomial.notMem_support_iff.mp hi, coefficientMass_zero]
    exact Nat.zero_le _

theorem le_degree_coeff (p : (ℤ[X])[X]) (D H : ℕ) (hD : p.natDegree ≤ D)
    (hH : ∀ i, coefficientMass (p.coeff i) ≤ H) : mass p ≤ (D + 1) * H := by
  rw [range_sum p (D + 1) (by omega)]
  exact (Finset.sum_le_sum (fun i _ => hH i)).trans_eq (by simp)

theorem le_pow (p : (ℤ[X])[X]) (D b : ℕ) (hD : p.natDegree ≤ D)
    (hb : ∀ i, coefficientMass (p.coeff i) ≤ 2 ^ b) : mass p ≤ 2 ^ (b + (D + 1).size) := by
  calc
    _ ≤ (D + 1) * 2 ^ b := le_degree_coeff p D _ hD hb
    _ ≤ 2 ^ (D + 1).size * 2 ^ b := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _ = _ := by rw [← pow_add, Nat.add_comm]

theorem add_le (p q : (ℤ[X])[X]) : mass (p + q) ≤ mass p + mass q := by
  let N := max p.natDegree q.natDegree + 1
  have hp : p.natDegree < N := by dsimp [N]; omega
  have hq : q.natDegree < N := by dsimp [N]; omega
  have hs : (p + q).natDegree < N := (natDegree_add_le p q).trans_lt (by dsimp [N]; omega)
  rw [range_sum (p + q) N hs, range_sum p N hp, range_sum q N hq, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by simpa only [coeff_add] using coefficientMass_add_le (p.coeff i) (q.coeff i)

@[simp] theorem neg (p : (ℤ[X])[X]) : mass (-p) = mass p := by
  rw [mass, mass, Polynomial.sum_def, Polynomial.sum_def]
  simp only [Polynomial.support_neg, Polynomial.coeff_neg, coefficientMass_neg]

theorem sub_le (p q : (ℤ[X])[X]) : mass (p - q) ≤ mass p + mass q := by
  simpa only [sub_eq_add_neg, neg] using add_le p (-q)

theorem sum_le {ι : Type*} (s : Finset ι) (f : ι → (ℤ[X])[X]) : mass (∑ i ∈ s, f i) ≤ ∑ i ∈ s, mass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (add_le _ _).trans (Nat.add_le_add_left ih _)

theorem mul_le (p q : (ℤ[X])[X]) : mass (p * q) ≤ mass p * mass q := by
  classical
  rw [Polynomial.mul_eq_sum_sum]
  simp only [Polynomial.sum_def]
  calc
    _ ≤ ∑ i ∈ p.support, mass (∑ j ∈ q.support, Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) := sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, mass (Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) :=
      Finset.sum_le_sum fun i _ => sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, coefficientMass (p.coeff i) * coefficientMass (q.coeff j) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun j _ => by simpa only [monomial] using coefficientMass_mul_le (p.coeff i) (q.coeff j)
    _ = _ := by
      rw [mass, mass, Polynomial.sum_def, Polynomial.sum_def, Finset.sum_mul]
      simp only [Finset.mul_sum]

theorem prod_le {ι : Type*} (s : Finset ι) (f : ι → (ℤ[X])[X]) : mass (∏ i ∈ s, f i) ≤ ∏ i ∈ s, mass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, ← Polynomial.C_1, C, coefficientMass_C]; decide
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem pow_le (p : (ℤ[X])[X]) (n : ℕ) : mass (p ^ n) ≤ mass p ^ n := by
  induction n with
  | zero => simp only [pow_zero, ← Polynomial.C_1, C, coefficientMass_C]; decide
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

theorem derivative_le (p : (ℤ[X])[X]) : mass p.derivative ≤ p.natDegree * mass p := by
  have hd : p.derivative = ∑ i ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial i (p.coeff i)).derivative := by
    conv_lhs => rw [p.as_sum_range]
    rw [derivative_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), mass ((Polynomial.monomial i (p.coeff i)).derivative) := by
      rw [hd]
      exact sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), coefficientMass (p.coeff i) * i := by
      apply Finset.sum_le_sum
      intro i _
      rw [derivative_monomial, monomial]
      change coefficientMass (p.coeff i * Polynomial.C (i : ℤ)) ≤ _
      simpa only [coefficientMass_C, Int.natAbs_natCast] using coefficientMass_mul_le (p.coeff i) (Polynomial.C (i : ℤ))
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), coefficientMass (p.coeff i) * p.natDegree :=
      Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (by have := Finset.mem_range.mp hi; omega)
    _ = _ := by rw [← Finset.sum_mul, ← range_sum p (p.natDegree + 1) (by omega), mul_comm]

theorem mono_coeff (p q : (ℤ[X])[X])
    (h : ∀ i, coefficientMass (p.coeff i) ≤ coefficientMass (q.coeff i)) : mass p ≤ mass q := by
  let N := max p.natDegree q.natDegree + 1
  rw [range_sum p N (by dsimp [N]; omega), range_sum q N (by dsimp [N]; omega)]
  exact Finset.sum_le_sum fun i _ => h i

theorem low_le (p : (ℤ[X])[X]) (d : ℕ) : mass (PseudoRemainder.low d p) ≤ mass p := by
  apply mono_coeff
  intro i
  rw [PseudoRemainder.low_coeff]
  split_ifs
  · exact le_rfl
  · simp

theorem high_le (p : (ℤ[X])[X]) (d : ℕ) : mass (PseudoRemainder.high d p) ≤ mass p := by
  by_cases hd : d ≤ p.natDegree
  · let N := p.natDegree - d + 1
    have hN : p.natDegree + 1 = d + N := by dsimp [N]; omega
    rw [range_sum (PseudoRemainder.high d p) N (by rw [PseudoRemainder.high_natDegree]; dsimp [N]; omega)]
    simp only [PseudoRemainder.high_coeff]
    have he : mass p = (∑ i ∈ Finset.range d, coefficientMass (p.coeff i)) +
        ∑ i ∈ Finset.range N, coefficientMass (p.coeff (i + d)) := by
      rw [range_sum p (p.natDegree + 1) (by omega), hN, Finset.sum_range_add]
      simp only [Nat.add_comm]
    rw [he]
    omega
  · have hz : PseudoRemainder.high d p = 0 := by
      apply Polynomial.ext
      intro i
      rw [PseudoRemainder.high_coeff, coeff_zero]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, zero]
    exact Nat.zero_le _

theorem step_le (p g : (ℤ[X])[X]) (d : ℕ) : mass (PseudoRemainder.step p d g) ≤ 2 * mass p * mass g := by
  calc
    _ ≤ mass (Polynomial.C (p.coeff d) * PseudoRemainder.low d g) +
        mass (PseudoRemainder.low d p * PseudoRemainder.high d g) := sub_le _ _
    _ ≤ coefficientMass (p.coeff d) * mass (PseudoRemainder.low d g) +
        mass (PseudoRemainder.low d p) * mass (PseudoRemainder.high d g) := by
      exact Nat.add_le_add (by simpa only [C] using mul_le (Polynomial.C (p.coeff d)) (PseudoRemainder.low d g)) (mul_le _ _)
    _ ≤ mass p * mass g + mass p * mass g :=
      Nat.add_le_add (Nat.mul_le_mul (coeff_le p d) (low_le g d)) (Nat.mul_le_mul (low_le p d) (high_le g d))
    _ = _ := by ring

theorem iterate_le (p g : (ℤ[X])[X]) (d n : ℕ) :
    mass ((PseudoRemainder.step p d)^[n] g) ≤ (2 * mass p) ^ n * mass g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    exact (step_le p _ d).trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left (2 * mass p) ih)

private theorem unit_smul (u : ℤˣ) (p : (ℤ[X])[X]) : mass (u • p) = mass p := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h, Units.smul_def, neg]

/-- The Leibniz bound on total integer mass of a bivariate determinant. -/
theorem det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ℤ[X])[X]) (M : ℕ) (hM : ∀ r s, mass (A r s) ≤ M) :
    mass A.det ≤ (Fintype.card ι).factorial * M ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, mass (Equiv.Perm.sign σ • ∏ j, A (σ j) j) := sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ _j : ι, M := by
      apply Finset.sum_le_sum
      intro σ _
      rw [unit_smul]
      exact (prod_le _ _).trans (Finset.prod_le_prod (fun j _ => hM (σ j) j))
    _ = _ := by simp [Fintype.card_perm]

end LeanCanny.Algebra.NestedMass
