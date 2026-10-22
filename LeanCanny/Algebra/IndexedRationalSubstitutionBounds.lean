/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IndexedRationalSubstitution
public import LeanCanny.Algebra.CoefficientMass
import Mathlib.Tactic.Ring

/-!
# Degree and coefficient budgets for indexed rational substitution

For `M` source terms in `A` variables with exponents at most the clearing width
`W`, coordinate degrees at most `E` give degree at most `A*W*E`. Source magnitude
bits `s` and coordinate coefficient-mass bits `b` give coefficient magnitude-bit
length at most `M.size+s+A*W*b+1`. Repeated or cancelling terms are allowed.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution.Indexed
open Polynomial
open scoped BigOperators

theorem natDegree_cleared_le {R : Type*} [CommSemiring R] (A M W E : ℕ)
    (a : ℕ → R) (e : ℕ → ℕ → ℕ) (n d : ℕ → R[X])
    (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ W)
    (hn : ∀ i, i < A → (n i).natDegree ≤ E) (hd : ∀ i, i < A → (d i).natDegree ≤ E) :
    (cleared A M W a e n d).natDegree ≤ A * W * E := by
  classical
  unfold cleared
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r hr
  have hr' := Finset.mem_range.mp hr
  calc
    _ ≤ (C (a r)).natDegree + (∏ i ∈ Finset.range A, n i ^ e r i * d i ^ (W - e r i)).natDegree :=
      Polynomial.natDegree_mul_le
    _ = (∏ i ∈ Finset.range A, n i ^ e r i * d i ^ (W - e r i)).natDegree := by
      simp only [Polynomial.natDegree_C, Nat.zero_add]
    _ ≤ ∑ i ∈ Finset.range A, (n i ^ e r i * d i ^ (W - e r i)).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i ∈ Finset.range A, W * E := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      calc
        _ ≤ (n i ^ e r i).natDegree + (d i ^ (W - e r i)).natDegree := Polynomial.natDegree_mul_le
        _ ≤ e r i * (n i).natDegree + (W - e r i) * (d i).natDegree :=
          Nat.add_le_add Polynomial.natDegree_pow_le Polynomial.natDegree_pow_le
        _ ≤ e r i * E + (W - e r i) * E :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (hn i hi')) (Nat.mul_le_mul_left _ (hd i hi'))
        _ = W * E := by rw [← Nat.add_mul, Nat.add_sub_of_le (he r hr' i hi')]
    _ = A * W * E := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_assoc]

theorem coefficientMass_cleared_le_pow (A M W s b : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ) (n d : ℕ → ℤ[X])
    (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ W)
    (ha : ∀ r, r < M → (a r).natAbs ≤ 2 ^ s)
    (hn : ∀ i, i < A → coefficientMass (n i) ≤ 2 ^ b)
    (hd : ∀ i, i < A → coefficientMass (d i) ≤ 2 ^ b) :
    coefficientMass (cleared A M W a e n d) ≤ 2 ^ (M.size + s + A * W * b) := by
  classical
  have hfactor (r i : ℕ) (hr : r < M) (hi : i < A) :
      coefficientMass (n i ^ e r i * d i ^ (W - e r i)) ≤ 2 ^ (W * b) := by
    calc
      _ ≤ coefficientMass (n i ^ e r i) * coefficientMass (d i ^ (W - e r i)) := coefficientMass_mul_le _ _
      _ ≤ coefficientMass (n i) ^ e r i * coefficientMass (d i) ^ (W - e r i) :=
        Nat.mul_le_mul (coefficientMass_pow_le _ _) (coefficientMass_pow_le _ _)
      _ ≤ (2 ^ b) ^ e r i * (2 ^ b) ^ (W - e r i) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (hn i hi) _) (Nat.pow_le_pow_left (hd i hi) _)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le (he r hr i hi), ← pow_mul, Nat.mul_comm]
  have hprod (r : ℕ) (hr : r < M) :
      coefficientMass (∏ i ∈ Finset.range A, n i ^ e r i * d i ^ (W - e r i)) ≤ 2 ^ (A * W * b) := by
    calc
      _ ≤ ∏ i ∈ Finset.range A, coefficientMass (n i ^ e r i * d i ^ (W - e r i)) := coefficientMass_prod_le _ _
      _ ≤ ∏ _i ∈ Finset.range A, 2 ^ (W * b) :=
        Finset.prod_le_prod (fun i hi => hfactor r i hr (Finset.mem_range.mp hi))
      _ = _ := by simp only [Finset.prod_const, Finset.card_range, ← pow_mul]; congr 1; ring
  have hterm (r : ℕ) (hr : r < M) :
      coefficientMass (C (a r) * ∏ i ∈ Finset.range A, n i ^ e r i * d i ^ (W - e r i)) ≤ 2 ^ (s + A * W * b) := by
    apply (coefficientMass_mul_le _ _).trans
    rw [coefficientMass_C, pow_add]
    exact Nat.mul_le_mul (ha r hr) (hprod r hr)
  calc
    _ ≤ ∑ r ∈ Finset.range M,
        coefficientMass (C (a r) * ∏ i ∈ Finset.range A, n i ^ e r i * d i ^ (W - e r i)) := coefficientMass_sum_le _ _
    _ ≤ ∑ _r ∈ Finset.range M, 2 ^ (s + A * W * b) :=
      Finset.sum_le_sum (fun r hr => hterm r (Finset.mem_range.mp hr))
    _ = M * 2 ^ (s + A * W * b) := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ 2 ^ M.size * 2 ^ (s + A * W * b) := Nat.mul_le_mul_right _ (Nat.lt_size_self M).le
    _ = _ := by rw [← pow_add, Nat.add_assoc]

theorem coeff_size_cleared_le (A M W s b : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ) (n d : ℕ → ℤ[X])
    (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ W)
    (ha : ∀ r, r < M → (a r).natAbs ≤ 2 ^ s)
    (hn : ∀ i, i < A → coefficientMass (n i) ≤ 2 ^ b)
    (hd : ∀ i, i < A → coefficientMass (d i) ≤ 2 ^ b) (k : ℕ) :
    ((cleared A M W a e n d).coeff k).natAbs.size ≤ M.size + s + A * W * b + 1 := by
  have h := (coeff_natAbs_le_coefficientMass (cleared A M W a e n d) k).trans
    (coefficientMass_cleared_le_pow A M W s b a e n d he ha hn hd)
  simpa only [Nat.size_pow] using Nat.size_le_size h

end LeanCanny.Algebra.RationalSubstitution.Indexed
