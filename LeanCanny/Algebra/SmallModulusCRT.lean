/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ChineseRemainderSign

/-!
# Small prime-power moduli for integer sign reconstruction

The maximal powers of primes up to `N` form a coprime CRT system with product
`lcmUpto N`, while each individual modulus is at most `N`. For a `B`-bit integer,
`N = 2*B+6` suffices for centered reconstruction. A concrete dyadic precision
reduces its sign to the truncated-quotient comparison from `ChineseRemainderSign`.
Neither the combined modulus nor the full precision word is claimed to fit in
polynomial space; their bit access must be implemented by a streamed algorithm.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder

open scoped BigOperators

abbrev SmallPrime (N : ℕ) := {p : ℕ // p ∈ Nat.primesLE N}

def primePowerSystem (N : ℕ) : System (SmallPrime N) where
  modulus p := p.val ^ p.val.log N
  positive p := pow_pos (Nat.prime_of_mem_primesLE p.property).pos _
  coprime p q hpq := Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primesLE p.property)
    (Nat.prime_of_mem_primesLE q.property) (by exact fun h => hpq (Subtype.ext h))

theorem primePowerSystem_product (N : ℕ) : (primePowerSystem N).product = Nat.lcmUpto N := by
  rw [Nat.lcmUpto_eq_prod_pow_log]
  exact Finset.prod_coe_sort (Nat.primesLE N) (fun p => p ^ p.log N)

theorem primePowerSystem_modulus_le (N : ℕ) (p : SmallPrime N) :
    (primePowerSystem N).modulus p ≤ N := by
  have hp := Nat.le_of_mem_primesLE p.property
  have hprime := Nat.prime_of_mem_primesLE p.property
  have := hprime.pos
  exact Nat.pow_log_le_self _ (by omega)

theorem smallPrime_card_le (N : ℕ) : Fintype.card (SmallPrime N) ≤ N + 1 := by
  rw [Fintype.card_coe, Nat.primesLE_eq_filter_range]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- The precision exponent has a short binary representation even when `N`
is exponential in the original input length. -/
def precisionBits (N : ℕ) : ℕ := (N + 2) * N.size + 2

theorem primePowerSystem_product_le (N : ℕ) :
    (primePowerSystem N).product ≤ 2 ^ ((N + 1) * N.size) := by
  calc
    _ ≤ ∏ _p : SmallPrime N, 2 ^ N.size := Finset.prod_le_prod (fun p _ =>
      (primePowerSystem_modulus_le N p).trans (Nat.size_le.mp (le_refl N.size)).le)
    _ = 2 ^ (Fintype.card (SmallPrime N) * N.size) := by
      rw [Finset.prod_const, Finset.card_univ, ← pow_mul, Nat.mul_comm N.size]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (smallPrime_card_le N))

theorem precision_sufficient (N : ℕ) :
    2 * Fintype.card (SmallPrime N) * (primePowerSystem N).product < 2 ^ precisionBits N := by
  have hcard : Fintype.card (SmallPrime N) ≤ 2 ^ N.size :=
    (smallPrime_card_le N).trans (by have := Nat.size_le.mp (le_refl N.size); omega)
  calc
    _ ≤ (2 * 2 ^ N.size) * 2 ^ ((N + 1) * N.size) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hcard) (primePowerSystem_product_le N)
    _ = 2 ^ ((N + 2) * N.size + 1) := by rw [← pow_succ', ← pow_add]; congr 1; ring
    _ < _ := Nat.pow_lt_pow_right (by decide) (by dsimp only [precisionBits]; omega)

theorem negative_iff_small_truncated (z : ℤ) (B : ℕ) (hb : z.natAbs.size ≤ B) (hne : z ≠ 0)
    (r : SmallPrime (2 * B + 6) → ℕ)
    (hr : ∀ p, (r p : ZMod ((primePowerSystem (2 * B + 6)).modulus p)) = z) :
    z < 0 ↔ 2 ^ precisionBits (2 * B + 6) <
      2 * ((primePowerSystem (2 * B + 6)).truncatedSum r (2 ^ precisionBits (2 * B + 6)) %
        2 ^ precisionBits (2 * B + 6)) := by
  apply System.negative_iff_truncated_mod _ r z hr _ hne _ (by positivity) (precision_sufficient _)
  rw [primePowerSystem_product]
  exact IntegerModular.two_natAbs_lt_lcmUpto z B hb

end LeanCanny.Algebra.ChineseRemainder
