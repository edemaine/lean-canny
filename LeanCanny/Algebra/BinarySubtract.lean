/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BinaryProduct
import Mathlib.Tactic.Linarith

/-!
# A selected subtraction bit as a three-term sum

Finite-width complementation turns `a-b` into `a+complement(b)+1` modulo
the selected bit's enclosing power of two, provided `b≤a`. Complement bits
are direct negated source bits under a width guard, so the streamed sum-bit
machine supplies both the subtraction bit and its carry accounting.
-/

@[expose] public section

namespace LeanCanny.Algebra.BinarySubtract
open scoped BigOperators

def complement (b w : ℕ) : ℕ := 2 ^ w - 1 - b % 2 ^ w

def term (a b k i : ℕ) : ℕ :=
  if i = 0 then a else if i = 1 then complement b (k + 1) else if i = 2 then 1 else 0

theorem complement_bit (b w j : ℕ) :
    (complement b w).testBit j = (decide (j < w) && !(b.testBit j)) := by
  unfold complement
  rw [Nat.sub_sub, Nat.add_comm 1, Nat.testBit_two_pow_sub_succ (Nat.mod_lt b (by positivity)),
    Nat.testBit_mod_two_pow]
  by_cases hj : j < w <;> simp [hj]

theorem sum_term (a b k : ℕ) : (∑ i ∈ Finset.range 3, term a b k i) = a + complement b (k + 1) + 1 := by
  simp [term, Finset.sum_range_succ]

theorem subtract_mod (a b w : ℕ) (hab : b ≤ a) :
    (a + complement b w + 1) % 2 ^ w = (a - b) % 2 ^ w := by
  have hp : 0 < 2 ^ w := by positivity
  have hrem := Nat.mod_lt b hp
  have hcomp := Nat.sub_add_cancel (by omega : b % 2 ^ w ≤ 2 ^ w - 1)
  have hpow := Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ w)
  have hsub := Nat.sub_add_cancel hab
  have hmod := Nat.mod_add_div b (2 ^ w)
  have he : a + complement b w + 1 = (a - b) + 2 ^ w * (b / 2 ^ w + 1) := by
    unfold complement
    nlinarith
  rw [he, Nat.add_mul_mod_self_left]

theorem subtraction_bit (a b k : ℕ) (hab : b ≤ a) :
    (∑ i ∈ Finset.range 3, term a b k i).testBit k = (a - b).testBit k := by
  have he := subtract_mod a b (k + 1) hab
  have hb := congrArg (fun n => n.testBit k) he
  rw [sum_term]
  simpa only [Nat.testBit_mod_two_pow, Nat.lt_add_one, decide_true, Bool.true_and] using hb

end LeanCanny.Algebra.BinarySubtract
