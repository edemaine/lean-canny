/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SmallModulusCRT

/-!
# CRT moduli indexed by a simple bounded counter

Index every natural `i≤N`, using its maximal prime power when `i` is prime and
modulus one otherwise. The count is exactly `N+1`, so an implementation needs
no prime-counting routine or compressed enumeration of primes. Modulus one
contributes a zero numerator and preserves pairwise coprimality and the product.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder
open scoped BigOperators

def indexedModulus (N i : ℕ) : ℕ := if i.Prime then i ^ i.log N else 1

def indexedSystem (N : ℕ) : System (Fin (N + 1)) where
  modulus i := indexedModulus N i.val
  positive i := by
    unfold indexedModulus
    split_ifs with hp
    · exact pow_pos hp.pos _
    · decide
  coprime i j hij := by
    dsimp only [indexedModulus]
    split_ifs with hp hq
    · exact Nat.coprime_pow_primes _ _ hp hq (fun h => hij (Fin.ext h))
    · exact Nat.coprime_one_right _
    · exact Nat.coprime_one_left _
    · decide

theorem indexedSystem_product (N : ℕ) : (indexedSystem N).product = Nat.lcmUpto N := by
  change (∏ i : Fin (N + 1), indexedModulus N i.val) = _
  rw [← Finset.prod_range]
  simp only [indexedModulus]
  rw [← Finset.prod_filter, ← Nat.primesLE_eq_filter_range, ← Nat.lcmUpto_eq_prod_pow_log]

theorem indexedModulus_le (N i : ℕ) (hN : 0 < N) : indexedModulus N i ≤ N := by
  unfold indexedModulus
  split_ifs
  · exact Nat.pow_log_le_self _ hN.ne'
  · omega

theorem indexed_precision_sufficient (N : ℕ) :
    2 * Fintype.card (Fin (N + 1)) * (indexedSystem N).product < 2 ^ precisionBits N := by
  have hcard : N + 1 ≤ 2 ^ N.size := by have := Nat.lt_size_self N; omega
  have hp : (indexedSystem N).product ≤ 2 ^ ((N + 1) * N.size) := by
    rw [indexedSystem_product, ← primePowerSystem_product]
    exact primePowerSystem_product_le N
  rw [Fintype.card_fin]
  calc
    _ ≤ (2 * 2 ^ N.size) * 2 ^ ((N + 1) * N.size) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hcard) hp
    _ = 2 ^ ((N + 2) * N.size + 1) := by rw [← pow_succ', ← pow_add]; congr 1; ring
    _ < _ := Nat.pow_lt_pow_right (by decide) (by dsimp only [precisionBits]; omega)

theorem indexed_magnitude_bound (z : ℤ) (B : ℕ) (hb : z.natAbs.size ≤ B) :
    2 * z.natAbs < (indexedSystem (2 * B + 6)).product := by
  rw [indexedSystem_product]
  exact IntegerModular.two_natAbs_lt_lcmUpto z B hb

end LeanCanny.Algebra.ChineseRemainder
