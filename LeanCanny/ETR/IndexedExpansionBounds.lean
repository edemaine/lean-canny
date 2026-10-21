/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.IndexedExpansion
import Mathlib.Tactic.Linarith

/-!
# Bounds and finite-variable semantics for expression-tree monomials

Each exponent is bounded by the syntax degree bound, and variables outside the
syntax arity have exponent zero. The monomial count is at most exponential in
the number of leaves. Individual indexed coefficients have an additive bit
budget, even though collecting equal monomials can increase their coefficients.
-/

@[expose] public section

namespace LeanCanny.ETR.Term
open scoped BigOperators

def leafCount : Term → ℕ
  | .const _ | .var _ => 1
  | .add a b | .mul a b => a.leafCount + b.leafCount

def indexedCoefficientBits : Term → ℕ
  | .const z => z.natAbs.size
  | .var _ => 0
  | .add a b => max a.indexedCoefficientBits b.indexedCoefficientBits
  | .mul a b => a.indexedCoefficientBits + b.indexedCoefficientBits

theorem leafCount_pos (t : Term) : 0 < t.leafCount := by
  induction t <;> simp_all [leafCount]

theorem leafCount_le_dataSize (t : Term) : t.leafCount ≤ t.toData.size := by
  induction t with
  | const z => exact LeanCanny.Data.size_pos
  | var i => simp [leafCount]
  | add a b ha hb => simp only [leafCount, dataSize_add]; omega
  | mul a b ha hb => simp only [leafCount, dataSize_mul]; omega

theorem monomialCount_le_pow_leafCount (t : Term) : t.monomialCount ≤ 2 ^ t.leafCount := by
  induction t with
  | const z | var z => simp only [monomialCount, leafCount]; decide
  | add a b ha hb =>
    have hA : 2 ≤ 2 ^ a.leafCount := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) a.leafCount_pos
    have hB : 2 ≤ 2 ^ b.leafCount := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) b.leafCount_pos
    simp only [monomialCount, leafCount, pow_add]
    nlinarith
  | mul a b ha hb =>
    simpa only [monomialCount, leafCount, pow_add] using Nat.mul_le_mul ha hb

theorem monomialCount_size_le (t : Term) : t.monomialCount.size ≤ t.toData.size + 1 := by
  have h := (Nat.size_le_size (t.monomialCount_le_pow_leafCount)).trans
    (Nat.size_le_size (Nat.pow_le_pow_right (by decide : 1 ≤ 2) t.leafCount_le_dataSize))
  simpa only [Nat.size_pow] using h

theorem monomialCoefficient_natAbs_le (t : Term) (r : ℕ) :
    (t.monomialCoefficient r).natAbs ≤ 2 ^ t.indexedCoefficientBits := by
  induction t generalizing r with
  | const z => exact (Nat.lt_size_self z.natAbs).le
  | var i => simp [monomialCoefficient, indexedCoefficientBits]
  | add a b ha hb =>
    simp only [monomialCoefficient, indexedCoefficientBits]
    split_ifs
    · exact (ha _).trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
    · exact (hb _).trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  | mul a b ha hb =>
    simp only [monomialCoefficient, indexedCoefficientBits, Int.natAbs_mul, pow_add]
    exact Nat.mul_le_mul (ha _) (hb _)

theorem monomialExponent_le (t : Term) (r i : ℕ) : t.monomialExponent r i ≤ t.degreeBound := by
  induction t generalizing r with
  | const z => exact Nat.le_refl _
  | var j => simp only [monomialExponent, degreeBound]; split_ifs <;> omega
  | add a b ha hb =>
    simp only [monomialExponent, degreeBound]
    split_ifs
    · exact (ha _).trans (Nat.le_max_left _ _)
    · exact (hb _).trans (Nat.le_max_right _ _)
  | mul a b ha hb => exact Nat.add_le_add (ha _) (hb _)

theorem monomialExponent_eq_zero_of_arity_le (t : Term) (r i : ℕ) (hi : t.arity ≤ i) :
    t.monomialExponent r i = 0 := by
  induction t generalizing r with
  | const z => rfl
  | var j =>
    have h : i ≠ j := by simp only [arity] at hi; omega
    simp only [monomialExponent, h, ↓reduceIte]
  | add a b ha hb =>
    simp only [arity, max_le_iff] at hi
    simp only [monomialExponent]
    split_ifs <;> first | exact ha _ hi.1 | exact hb _ hi.2
  | mul a b ha hb =>
    simp only [arity, max_le_iff] at hi
    simp only [monomialExponent, ha _ hi.1, hb _ hi.2, Nat.zero_add]

theorem eval_eq_indexed_sum {R : Type*} [CommRing R] (t : Term) (env : ℕ → R)
    (A : ℕ) (hA : t.arity ≤ A) :
    t.eval env = ∑ r ∈ Finset.range t.monomialCount,
      (t.monomialCoefficient r : R) * ∏ i ∈ Finset.range A, env i ^ t.monomialExponent r i := by
  classical
  rw [← eval₂_toPolynomial, ← indexedMonomial_sum, MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [indexedMonomial, MvPolynomial.eval₂_monomial, Int.coe_castRingHom]
  congr 1
  have hsupport : (t.monomialPowers r).support ⊆ Finset.range A := by
    intro i hi
    apply Finset.mem_range.mpr
    by_contra h
    have hz := t.monomialExponent_eq_zero_of_arity_le r i (by omega)
    exact (Finsupp.mem_support_iff.mp hi) (by rw [monomialPowers_apply, hz])
  simpa only [monomialPowers_apply] using
    (t.monomialPowers r).prod_of_support_subset hsupport (fun i k => env i ^ k) (by simp)

theorem eval₂_indexed_source {R : Type*} [CommRing R] (t : Term) (env : ℕ → R)
    (A : ℕ) (hA : t.arity ≤ A) :
    (Algebra.RationalSubstitution.Indexed.source A t.monomialCount t.monomialCoefficient t.monomialExponent).eval₂
      (Int.castRingHom R) (fun i => env i.val) = t.eval env := by
  rw [Algebra.RationalSubstitution.Indexed.eval₂_source]
  exact (t.eval_eq_indexed_sum env A hA).symm

end LeanCanny.ETR.Term
