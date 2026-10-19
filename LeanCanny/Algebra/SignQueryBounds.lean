/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ScaledSignQueries
public import LeanCanny.Algebra.CoefficientMass
import Mathlib.Tactic.Ring

/-!
# Degree, coefficient, and output bounds for root-sign queries

Product-query exponents are at most two. Uniform degree and coefficient-mass
allowances therefore bound their degrees and integer coefficient sizes. Tarski
queries have magnitude at most the root degree. The scaled sign-pattern count
has at most `k + degree.size + 1` magnitude bits.
-/

@[expose] public section

namespace LeanCanny.Algebra.RootSignQueries
open Polynomial
open scoped BigOperators Classical

theorem map_queryPolynomial {R S J : Type*} [CommSemiring R] [CommSemiring S] [Fintype J]
    (φ : R →+* S) (Q : J → R[X]) (e : J → Fin 3) :
    (queryPolynomial Q e).map φ = queryPolynomial (fun i => (Q i).map φ) e := by
  simp only [queryPolynomial, Polynomial.map_prod, Polynomial.map_pow]

theorem natDegree_queryPolynomial_le {R J : Type*} [CommSemiring R] [Fintype J]
    (Q : J → R[X]) (e : J → Fin 3) (D : ℕ) (hD : ∀ i, (Q i).natDegree ≤ D) :
    (queryPolynomial Q e).natDegree ≤ 2 * Fintype.card J * D := by
  calc
    _ ≤ ∑ i, (Q i ^ (e i).val).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : J, 2 * D := by
      apply Finset.sum_le_sum
      intro i _
      exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul (by have := (e i).isLt; omega) (hD i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring

theorem coefficientMass_queryPolynomial_le {J : Type*} [Fintype J]
    (Q : J → ℤ[X]) (e : J → Fin 3) (b : ℕ) (hQ : ∀ i, coefficientMass (Q i) ≤ 2 ^ b) :
    coefficientMass (queryPolynomial Q e) ≤ 2 ^ (2 * Fintype.card J * b) := by
  calc
    _ ≤ ∏ i, coefficientMass (Q i ^ (e i).val) := coefficientMass_prod_le _ _
    _ ≤ ∏ _i : J, (2 ^ b) ^ 2 := by
      apply Finset.prod_le_prod
      intro i _
      exact (coefficientMass_pow_le _ _).trans ((Nat.pow_le_pow_left (hQ i) _).trans
        (Nat.pow_le_pow_right Nat.one_le_two_pow (by have := (e i).isLt; omega)))
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, ← pow_mul]; congr 1; ring

theorem coeff_size_queryPolynomial_le {J : Type*} [Fintype J]
    (Q : J → ℤ[X]) (e : J → Fin 3) (D b : ℕ)
    (hD : ∀ i, (Q i).natDegree ≤ D) (hQ : ∀ i k, ((Q i).coeff k).natAbs ≤ 2 ^ b) (k : ℕ) :
    ((queryPolynomial Q e).coeff k).natAbs.size ≤ 2 * Fintype.card J * (b + (D + 1).size) + 1 := by
  have h := (coeff_natAbs_le_coefficientMass (queryPolynomial Q e) k).trans
    (coefficientMass_queryPolynomial_le Q e _ (fun i => coefficientMass_le_pow_of_degree_coeff _ _ _ (hD i) (hQ i)))
  simpa only [Nat.size_pow] using Nat.size_le_size h

theorem signSum_bounds (Z : Finset ℝ) (q : ℝ[X]) : -(Z.card : ℤ) ≤ signSum Z q ∧ signSum Z q ≤ Z.card := by
  have hpoint (x : ℝ) : (-1 : ℤ) ≤ (SignType.sign (q.eval x) : ℤ) ∧ (SignType.sign (q.eval x) : ℤ) ≤ 1 := by
    cases SignType.sign (q.eval x) <;> decide
  have hu := Finset.sum_le_sum (s := Z) (fun x _ => (hpoint x).2)
  have hl := Finset.sum_le_sum (s := Z) (fun x _ => (hpoint x).1)
  simpa only [signSum, Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg_one] using And.intro hl hu

theorem tarskiQuery_bounds (p q : ℝ[X]) : -(p.natDegree : ℤ) ≤ tarskiQuery p q ∧ tarskiQuery p q ≤ p.natDegree := by
  have h := signSum_bounds p.roots.toFinset q
  have hcard : p.roots.toFinset.card ≤ p.natDegree :=
    (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)
  have hcast : (p.roots.toFinset.card : ℤ) ≤ p.natDegree := by omega
  exact ⟨(neg_le_neg hcast).trans h.1, h.2.trans hcast⟩

theorem root_signCount_le {J : Type*} (p : ℝ[X]) (Q : J → ℝ[X]) (σ : J → SignType) :
    signCount p.roots.toFinset Q σ ≤ p.natDegree :=
  (Finset.card_filter_le _ _).trans ((Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p))

theorem scaledRootCount_natAbs_size_le {J : Type*} [Fintype J] (p : ℝ[X]) (Q : J → ℝ[X]) (σ : J → SignType) :
    (scaledRootCount p Q σ).natAbs.size ≤ Fintype.card J + p.natDegree.size + 1 := by
  have heq : scaledRootCount p Q σ = ((2 ^ Fintype.card J * signCount p.roots.toFinset Q σ : ℕ) : ℤ) := by
    rw [scaledRootCount_eq]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [heq, Int.natAbs_natCast]
  have h : 2 ^ Fintype.card J * signCount p.roots.toFinset Q σ ≤ 2 ^ (Fintype.card J + p.natDegree.size) := by
    rw [pow_add]
    exact Nat.mul_le_mul_left _ ((root_signCount_le p Q σ).trans (Nat.lt_size_self p.natDegree).le)
  simpa only [Nat.size_pow] using Nat.size_le_size h

end LeanCanny.Algebra.RootSignQueries
