/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Ring.Parity

/-! # Even and odd products of binomial transforms

Binomial multiplicities balance between even and odd degrees except at
index zero. The resulting multiplicative identity needs only a commutative
monoid, so it applies to determinants without dividing or assuming they
are nonzero.
-/

@[expose] public section

namespace LeanCanny.Algebra.BinomialParityProducts
open scoped BigOperators Classical

theorem choose_even_odd_sum (N j : ℕ) (hj : j < N) :
    (∑ k ∈ Finset.range N, if Even k then j.choose k else 0) =
      (if j = 0 then 1 else 0) + ∑ k ∈ Finset.range N, if Even k then 0 else j.choose k := by
  have hext : (∑ k ∈ Finset.range (j + 1), (-1 : ℤ) ^ k * (j.choose k : ℤ)) =
      ∑ k ∈ Finset.range N, (-1 : ℤ) ^ k * (j.choose k : ℤ) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    have hkj : j < k := by
      simp only [Finset.mem_range, not_lt] at hk
      omega
    rw [Nat.choose_eq_zero_of_lt hkj, Nat.cast_zero, mul_zero]
  have halt := hext.symm.trans (Int.alternating_sum_range_choose (n := j))
  have hsplit :
      (∑ k ∈ Finset.range N, if Even k then (j.choose k : ℤ) else 0) -
      (∑ k ∈ Finset.range N, if Even k then 0 else (j.choose k : ℤ)) =
        if j = 0 then 1 else 0 := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_congr rfl (fun k _ => ?_)).trans halt
    by_cases hk : Even k <;> simp [hk, neg_one_pow_eq_ite]
  have heq := sub_eq_iff_eq_add.mp hsplit
  exact_mod_cast heq

theorem choose_even_odd_sum_fin (N : ℕ) (j : Fin N) :
    (∑ k : Fin N, if Even k.val then j.val.choose k.val else 0) =
      (if j.val = 0 then 1 else 0) + ∑ k : Fin N, if Even k.val then 0 else j.val.choose k.val := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if Even k then j.val.choose k else 0) N,
    Fin.sum_univ_eq_sum_range (fun k => if Even k then 0 else j.val.choose k) N]
  exact choose_even_odd_sum N j.val j.isLt

variable {M : Type*} [CommMonoid M]

theorem parity_product (N : ℕ) (a : Fin N → M) (P : ℕ → Prop) [DecidablePred P] :
    (∏ k : Fin N, if P k.val then ∏ j : Fin N, a j ^ (j.val.choose k.val) else 1) =
      ∏ j : Fin N, a j ^ (∑ k : Fin N, if P k.val then j.val.choose k.val else 0) := by
  calc
    _ = ∏ k : Fin N, ∏ j : Fin N, a j ^ (if P k.val then j.val.choose k.val else 0) := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : P k.val <;> simp [hk]
    _ = _ := by
      rw [Finset.prod_comm]
      apply Finset.prod_congr rfl
      intro j _
      exact Finset.prod_pow_eq_pow_sum _ _ _

theorem binomial_even_odd_product (N : ℕ) (a : Fin N → M) :
    (∏ k : Fin N, if Even k.val then ∏ j : Fin N, a j ^ (j.val.choose k.val) else 1) =
      (∏ j : Fin N, a j ^ (if j.val = 0 then 1 else 0)) *
        ∏ k : Fin N, if Even k.val then 1 else ∏ j : Fin N, a j ^ (j.val.choose k.val) := by
  rw [parity_product]
  calc
    _ = ∏ j : Fin N, a j ^ (if j.val = 0 then 1 else 0) *
        a j ^ (∑ k : Fin N, if Even k.val then 0 else j.val.choose k.val) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [choose_even_odd_sum_fin, pow_add]
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      have ho := parity_product N a (fun k => ¬Even k)
      simp only [ite_not] at ho
      rw [ho]

end LeanCanny.Algebra.BinomialParityProducts
