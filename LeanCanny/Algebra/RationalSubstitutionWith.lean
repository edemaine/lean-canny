/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionMap
public import LeanCanny.Algebra.RationalSubstitutionBounds

/-! # Explicit clearing allowances preserve evaluations and admit uniform budgets

The allowances may exceed the actual variable degrees and remain unchanged
under coefficient reduction. Degree and coefficient-mass estimates depend on
the supplied allowances and coordinate bounds, without recomputing degrees.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution
open Polynomial
open scoped BigOperators Classical
variable {σ R : Type*} [Fintype σ] [CommSemiring R]

theorem natDegree_clearedWith_le (D : σ → ℕ) (p : MvPolynomial σ R) (n d : σ → R[X])
    (hD : ∀ i, p.degreeOf i ≤ D i) (E : ℕ)
    (hn : ∀ i, (n i).natDegree ≤ E) (hd : ∀ i, (d i).natDegree ≤ E) :
    (clearedWith D p n d).natDegree ≤ (∑ i, 2 * D i) * E := by
  unfold clearedWith
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  apply Polynomial.natDegree_mul_le.trans
  rw [Polynomial.natDegree_C, zero_add, Finset.sum_mul]
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hf : e i ≤ 2 * D i :=
    ((MvPolynomial.monomial_le_degreeOf i he).trans (hD i)).trans (by omega)
  calc
    _ ≤ (n i ^ e i).natDegree + (d i ^ (2 * D i - e i)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ e i * (n i).natDegree + (2 * D i - e i) * (d i).natDegree :=
      Nat.add_le_add Polynomial.natDegree_pow_le Polynomial.natDegree_pow_le
    _ ≤ e i * E + (2 * D i - e i) * E :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (hn i)) (Nat.mul_le_mul_left _ (hd i))
    _ = 2 * D i * E := by rw [← Nat.add_mul, Nat.add_sub_of_le hf]

theorem coefficientMass_clearedWith_le_pow (D : σ → ℕ) (p : MvPolynomial σ ℤ)
    (n d : σ → ℤ[X]) (hD : ∀ i, p.degreeOf i ≤ D i) (s b : ℕ)
    (hp : sourceMass p ≤ 2 ^ s)
    (hn : ∀ i, coefficientMass (n i) ≤ 2 ^ b) (hd : ∀ i, coefficientMass (d i) ≤ 2 ^ b) :
    coefficientMass (clearedWith D p n d) ≤ 2 ^ (s + (∑ i, 2 * D i) * b) := by
  have hf (e : σ →₀ ℕ) (he : e ∈ p.support) (i : σ) :
      coefficientMass (n i ^ e i * d i ^ (2 * D i - e i)) ≤ (2 ^ b) ^ (2 * D i) := by
    have hle : e i ≤ 2 * D i :=
      ((MvPolynomial.monomial_le_degreeOf i he).trans (hD i)).trans (by omega)
    apply (coefficientMass_mul_le _ _).trans
    apply (Nat.mul_le_mul (coefficientMass_pow_le _ _) (coefficientMass_pow_le _ _)).trans
    apply (Nat.mul_le_mul (Nat.pow_le_pow_left (hn i) _) (Nat.pow_le_pow_left (hd i) _)).trans_eq
    rw [← pow_add, Nat.add_sub_of_le hle]
  calc
    _ ≤ ∑ e ∈ p.support, coefficientMass (C (p.coeff e) * ∏ i, n i ^ e i * d i ^ (2 * D i - e i)) :=
      coefficientMass_sum_le _ _
    _ ≤ ∑ e ∈ p.support, (p.coeff e).natAbs * ∏ i, (2 ^ b) ^ (2 * D i) := by
      apply Finset.sum_le_sum
      intro e he
      apply (coefficientMass_mul_le _ _).trans
      rw [coefficientMass_C]
      exact Nat.mul_le_mul_left _ ((coefficientMass_prod_le _ _).trans (Finset.prod_le_prod (fun i _ => hf e he i)))
    _ = sourceMass p * ∏ i, (2 ^ b) ^ (2 * D i) := by rw [← Finset.sum_mul]; rfl
    _ ≤ 2 ^ s * ∏ i, (2 ^ b) ^ (2 * D i) := Nat.mul_le_mul_right _ hp
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, ← pow_add, Nat.mul_comm b]

end LeanCanny.Algebra.RationalSubstitution
