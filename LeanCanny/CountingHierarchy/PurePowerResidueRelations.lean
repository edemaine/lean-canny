/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PurePowerResidue
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-!
# The residue functional annihilates the pure-power relations

Shifting one geometric-series index telescopes the two terms of
`X_i^ell - r_i`. The missing lower face vanishes by its coordinate degree,
and the missing upper face vanishes by total degree. Thus the canonical
finite functional vanishes on the generated ideal over any coefficient ring.
-/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open MvPolynomial
open scoped Classical BigOperators

variable {S : Type*} [CommRing S] {n : ℕ}

@[expose] noncomputable def raiseIndex (j : Fin n → ℕ) (i : Fin n) : Fin n → ℕ :=
  Function.update j i (j i + 1)

@[expose] noncomputable def lowerIndex (j : Fin n → ℕ) (i : Fin n) : Fin n → ℕ :=
  Function.update j i (j i - 1)

theorem powerProduct_raise (r : Fin n → MvPolynomial (Fin n) S)
    (j : Fin n → ℕ) (i : Fin n) :
    (∏ k, r k ^ raiseIndex j i k) = (∏ k, r k ^ j k) * r i := by
  have heq (k : Fin n) : r k ^ raiseIndex j i k =
      r k ^ j k * (if k = i then r i else 1) := by
    by_cases hk : k = i
    · subst k
      simp [raiseIndex, pow_succ]
    · simp [raiseIndex, hk]
  simp_rw [heq]
  rw [Finset.prod_mul_distrib]
  simp

theorem target_raise (ell : ℕ) (j : Fin n → ℕ) (i : Fin n) :
    target ell (raiseIndex j i) = target ell j + Finsupp.single i ell := by
  ext k
  by_cases hk : k = i
  · subst k
    simp [target, raiseIndex, Nat.mul_add, Nat.add_assoc]
  · simp [target, raiseIndex, hk]

theorem term_raise (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S)
    (v : MvPolynomial (Fin n) S) (j : Fin n → ℕ) (i : Fin n) :
    term ell r (v * X i ^ ell) (raiseIndex j i) = term ell r (v * r i) j := by
  rw [term, powerProduct_raise, target_raise]
  have hmul : (v * X i ^ ell) * ((∏ k, r k ^ j k) * r i) =
      ((v * r i) * ∏ k, r k ^ j k) * X i ^ ell := by ring
  rw [hmul, X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial, mul_one]
  rfl

theorem term_axis_zero {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (v : MvPolynomial (Fin n) S)
    (j : Fin n → ℕ) (i : Fin n) (hj : j i = 0) :
    term ell r (v * X i ^ ell) j = 0 := by
  have hnot : ¬Finsupp.single i ell ≤ target ell j := by
    rw [Finsupp.single_le_iff]
    simp only [target, exponent_apply, hj, Nat.mul_zero, Nat.add_zero]
    omega
  rw [term]
  have hmul : (v * X i ^ ell) * (∏ k, r k ^ j k) =
      (v * ∏ k, r k ^ j k) * X i ^ ell := by ring
  rw [hmul, X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial', ite_eq_right hnot]

/-- The two filtered rectangular sums are exactly reindexed by incrementing
the selected coordinate. This equality itself needs no degree assumptions. -/
theorem shifted_sum (ell B : ℕ) (r : Fin n → MvPolynomial (Fin n) S)
    (v : MvPolynomial (Fin n) S) (i : Fin n) :
    (∑ j ∈ (indices n B).filter (fun j => j i < B), term ell r (v * r i) j) =
      ∑ j ∈ (indices n B).filter (fun j => 0 < j i), term ell r (v * X i ^ ell) j := by
  apply Finset.sum_bij (fun j _ => raiseIndex j i)
  · intro j hj
    obtain ⟨hj, hji⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    constructor
    · apply mem_indices.mpr
      intro k
      by_cases hk : k = i
      · subst k
        simp only [raiseIndex, Function.update_self]
        omega
      · simpa only [raiseIndex, Function.update_of_ne hk] using mem_indices.mp hj k
    · simp [raiseIndex]
  · intro j hj k hk heq
    funext a
    have hh := congrFun heq a
    by_cases ha : a = i
    · subst a
      simp only [raiseIndex, Function.update_self] at hh
      omega
    · simpa only [raiseIndex, Function.update_of_ne ha] using hh
  · intro k hk
    obtain ⟨hk, hki⟩ := Finset.mem_filter.mp hk
    have hl : lowerIndex k i ∈ (indices n B).filter (fun j => j i < B) := by
      apply Finset.mem_filter.mpr
      constructor
      · apply mem_indices.mpr
        intro a
        have haB := mem_indices.mp hk a
        by_cases ha : a = i
        · subst a
          simp only [lowerIndex, Function.update_self]
          omega
        · simpa only [lowerIndex, Function.update_of_ne ha] using haB
      · have hiB := mem_indices.mp hk i
        simp only [lowerIndex, Function.update_self]
        omega
    refine ⟨lowerIndex k i, hl, ?_⟩
    funext a
    by_cases ha : a = i
    · subst a
      simp only [raiseIndex, lowerIndex, Function.update_self]
      omega
    · simp only [raiseIndex, lowerIndex, Function.update_of_ne ha]
  · intro j _
    exact (term_raise ell r v j i).symm

/-- The canonical functional respects each defining reduction relation. -/
theorem residue_mul_X_pow {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) (i : Fin n) :
    residue ell r (v * X i ^ ell) = residue ell r (v * r i) := by
  let B := v.totalDegree + ell
  have hx : (X i ^ ell : MvPolynomial (Fin n) S).totalDegree ≤ ell := by
    rw [X_pow_eq_monomial]
    simpa using MvPolynomial.totalDegree_monomial_le (Finsupp.single i ell) (1 : S)
  have hleft : (v * X i ^ ell).totalDegree ≤ B :=
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add_left hx _)
  have hright : (v * r i).totalDegree < B :=
    (MvPolynomial.totalDegree_mul _ _).trans_lt (Nat.add_lt_add_left (hr i) _)
  rw [residue_eq_truncated hell r hr _ hleft,
    residue_eq_truncated hell r hr _ hright.le]
  change (∑ j ∈ indices n B, term ell r (v * X i ^ ell) j) =
    ∑ j ∈ indices n B, term ell r (v * r i) j
  have hL :
      (∑ j ∈ (indices n B).filter (fun j => 0 < j i), term ell r (v * X i ^ ell) j) =
        ∑ j ∈ indices n B, term ell r (v * X i ^ ell) j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hjnot
    have hji : j i = 0 := by
      have hnot : ¬0 < j i := fun h => hjnot (Finset.mem_filter.mpr ⟨hj, h⟩)
      omega
    exact term_axis_zero hell r v j i hji
  have hR :
      (∑ j ∈ (indices n B).filter (fun j => j i < B), term ell r (v * r i) j) =
        ∑ j ∈ indices n B, term ell r (v * r i) j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hjnot
    have hji : B ≤ j i := by
      have hnot : ¬j i < B := fun h => hjnot (Finset.mem_filter.mpr ⟨hj, h⟩)
      omega
    have hd : j i ≤ indexDegree j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact term_eq_zero_of_degree_lt hell r hr (v * r i) j (by omega)
  rw [← hL, ← hR, shifted_sum]

/-- The actual ideal of the pure-power relations. -/
@[expose] noncomputable def relationIdeal (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S) :
    Ideal (MvPolynomial (Fin n) S) := Ideal.span (Set.range (fun i => X i ^ ell - r i))

theorem linear_mul_generator {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) (i : Fin n) :
    linear hell r hr (v * (X i ^ ell - r i)) = 0 := by
  rw [mul_sub, map_sub]
  simp only [linear_apply]
  rw [residue_mul_X_pow hell r hr, sub_self]

/-- Vanishing on the generated ideal is proved for all polynomial multiples,
which is the induction invariant required by ideal closure. -/
theorem linear_mul_mem_ideal {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (q : MvPolynomial (Fin n) S) (hq : q ∈ relationIdeal ell r) :
    ∀ v, linear hell r hr (v * q) = 0 := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨i, rfl⟩ := hq
    intro v
    exact linear_mul_generator hell r hr v i
  | zero => intro v; rw [mul_zero, map_zero]
  | add q t hq ht ihq iht =>
    intro v
    rw [mul_add, map_add, ihq v, iht v, add_zero]
  | smul c q hq ih =>
    intro v
    change linear hell r hr (v * (c * q)) = 0
    simpa only [mul_assoc] using ih (v * c)

theorem linear_mem_ideal {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (q : MvPolynomial (Fin n) S) (hq : q ∈ relationIdeal ell r) :
    linear hell r hr q = 0 := by
  simpa only [one_mul] using linear_mul_mem_ideal hell r hr q hq 1

end LeanCanny.CountingHierarchy.PurePowerResidue
