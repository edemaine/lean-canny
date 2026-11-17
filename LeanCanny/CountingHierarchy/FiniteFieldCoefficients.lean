/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Foundations.NumberTheory.FiniteField.Enumeration
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Coefficients from finite-field evaluations

A polynomial of degree strictly below `card K - 1` has its indexed
coefficients recovered by one weighted sum over the field. The exponent is
positive, so the zero evaluation point contributes zero and needs no special
case. This is the one-variable coefficient-extraction identity used by
Sections 2 and 3 of the October 4, 2026 counting-hierarchy preprint.

This module proves the algebraic identity; its short-index computation and
counting-level bound are separate from the finite field's mathematical sum.
-/

public section

namespace LeanCanny.CountingHierarchy.FiniteFieldCoefficients

open Finset Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

private theorem sum_pow_positive (e : ℕ) (he : 0 < e) :
    (∑ x : K, x ^ e) = if Fintype.card K - 1 ∣ e then -1 else 0 := by
  let φ : Kˣ ↪ K := ⟨fun x => x, Units.val_injective⟩
  have hmap : univ.map φ = univ \ {(0 : K)} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and,
      mem_sdiff, mem_singleton, φ] using! isUnit_iff_ne_zero
  calc
    (∑ x : K, x ^ e) = ∑ x ∈ univ \ {(0 : K)}, x ^ e := by
      rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton,
        zero_pow (Nat.ne_of_gt he), add_zero]
    _ = ∑ x : Kˣ, (x ^ e : K) := by simp [φ, ← hmap, univ.sum_map φ]
    _ = _ := FiniteField.sum_pow_units K e

private theorem exponent_dvd_iff {m i k : ℕ} (hi : i < m) (hk : k < m) :
    m ∣ i + (m - k) ↔ i = k := by
  constructor
  · rintro ⟨t, ht⟩
    have htpos : 0 < t := by
      by_contra h
      have htzero : t = 0 := by omega
      simp only [htzero, mul_zero] at ht
      omega
    have htlt : t < 2 := by
      by_contra h
      have htwo : 2 ≤ t := by omega
      have hm := Nat.mul_le_mul_left m htwo
      omega
    have htone : t = 1 := by omega
    simp only [htone, mul_one] at ht
    omega
  · rintro rfl
    rw [Nat.add_sub_of_le hk.le]

/-- One field sum recovers any coefficient below the multiplicative period.
The condition on `k` is independent of the actual degree, so coefficients
above the degree are correctly recovered as zero. -/
theorem coeff_eq_neg_sum (P : Polynomial K) (k : ℕ)
    (hP : P.natDegree < Fintype.card K - 1)
    (hk : k < Fintype.card K - 1) :
    P.coeff k = -∑ x : K, P.eval x * x ^ (Fintype.card K - 1 - k) := by
  have he : 0 < Fintype.card K - 1 - k := by omega
  have hsum : (∑ x : K, P.eval x * x ^ (Fintype.card K - 1 - k)) = -P.coeff k := by
    simp_rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hterm (i : ℕ) (hi : i ∈ P.support) :
        (∑ x : K, (P.coeff i * x ^ i) * x ^ (Fintype.card K - 1 - k)) =
          if i = k then -P.coeff i else 0 := by
      simp_rw [mul_assoc, ← pow_add]
      rw [← Finset.mul_sum, sum_pow_positive _ (by omega)]
      simp only [exponent_dvd_iff ((Polynomial.le_natDegree_of_mem_supp i hi).trans_lt hP) hk]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hterm]
    by_cases hmem : k ∈ P.support
    · simp only [Finset.sum_ite_eq', hmem, ↓reduceIte]
    · simp only [Finset.sum_ite_eq', hmem, ↓reduceIte,
        Polynomial.notMem_support_iff.mp hmem, neg_zero]
  rw [hsum, neg_neg]

/-- Least natural representatives enumerate the same extraction sum over a prime field. -/
theorem coeff_eq_neg_sum_range {p : ℕ} [Fact p.Prime] (P : Polynomial (ZMod p)) (k : ℕ)
    (hP : P.natDegree < p - 1) (hk : k < p - 1) :
    P.coeff k = -∑ z ∈ Finset.range p, P.eval (z : ZMod p) *
      (z : ZMod p) ^ (p - 1 - k) := by
  calc
    P.coeff k = -∑ z : ZMod p, P.eval z * z ^ (p - 1 - k) := by
      simpa only [ZMod.card] using coeff_eq_neg_sum P k
        (by simpa only [ZMod.card] using hP) (by simpa only [ZMod.card] using hk)
    _ = _ := congrArg Neg.neg
      (ZMod.sum_range_natCast (fun z : ZMod p => P.eval z * z ^ (p - 1 - k))).symm

/-- Simultaneous multivariate coefficient extraction uses one grid sum, rather
than an input-dependent nesting of coefficient-extraction procedures. This
includes zero variables and coefficient indices outside the polynomial support. -/
theorem mv_coeff_eq_sum {n : ℕ} (P : MvPolynomial (Fin n) K) (β : Fin n →₀ ℕ)
    (hP : P.totalDegree < Fintype.card K - 1)
    (hβ : ∀ i, β i < Fintype.card K - 1) :
    P.coeff β = (-1 : K) ^ n * ∑ z : Fin n → K,
      MvPolynomial.eval z P * ∏ i, z i ^ (Fintype.card K - 1 - β i) := by
  classical
  have hsum : (∑ z : Fin n → K,
      MvPolynomial.eval z P * ∏ i, z i ^ (Fintype.card K - 1 - β i)) =
        P.coeff β * (-1 : K) ^ n := by
    simp_rw [MvPolynomial.eval_eq', Finset.sum_mul]
    rw [Finset.sum_comm]
    have hterm (e : Fin n →₀ ℕ) (he : e ∈ P.support) :
        (∑ z : Fin n → K, (P.coeff e * ∏ i, z i ^ e i) *
          ∏ i, z i ^ (Fintype.card K - 1 - β i)) =
          if e = β then P.coeff e * (-1 : K) ^ n else 0 := by
      have hei (i : Fin n) : e i < Fintype.card K - 1 :=
        ((Finsupp.single_eval_le_sum e rfl (fun _ => Nat.zero_le _) i).trans
          (MvPolynomial.le_totalDegree he)).trans_lt hP
      simp_rw [mul_assoc, ← Finset.prod_mul_distrib, ← pow_add]
      rw [← Finset.mul_sum,
        ← Fintype.prod_sum (fun (i : Fin n) (t : K) =>
          t ^ (e i + (Fintype.card K - 1 - β i)))]
      have hpowers (i : Fin n) :
          (∑ t : K, t ^ (e i + (Fintype.card K - 1 - β i))) =
            if e i = β i then -1 else 0 := by
        rw [sum_pow_positive _ (by have := hβ i; omega)]
        simp only [exponent_dvd_iff (hei i) (hβ i)]
      simp_rw [hpowers]
      by_cases heq : e = β
      · simp only [heq, ite_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      · obtain ⟨i, hi⟩ : ∃ i, e i ≠ β i := by
          by_contra h
          push Not at h
          exact heq (Finsupp.ext h)
        rw [ite_eq_right heq, Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi), mul_zero]
    rw [Finset.sum_congr rfl hterm]
    by_cases hmem : β ∈ P.support
    · simp only [Finset.sum_ite_eq', hmem, ↓reduceIte]
    · simp only [Finset.sum_ite_eq', hmem, ↓reduceIte,
        MvPolynomial.notMem_support_iff.mp hmem, zero_mul]
  rw [hsum, mul_left_comm, ← mul_pow]
  norm_num

end LeanCanny.CountingHierarchy.FiniteFieldCoefficients
