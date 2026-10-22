/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BinarySumCarry
public import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring

/-!
# A selected product bit as a sum of shifted terms

To read product bit `k`, retain the first `k+1` bits of the left factor.
Each resulting summand is a shifted copy of the right factor selected by
one left bit. Its own bit query needs only the two source bit queries.
-/

@[expose] public section

namespace LeanCanny.Algebra.BinaryProduct
open scoped BigOperators

def low (a w : ℕ) : ℕ := ∑ i ∈ Finset.range w, BinarySum.bit a i * 2 ^ i

def term (a b i : ℕ) : ℕ := if a.testBit i then b * 2 ^ i else 0

theorem div_step (a k : ℕ) :
    a / 2 ^ k = BinarySum.bit a k + 2 * (a / 2 ^ (k + 1)) := by
  have he := Nat.mod_add_div (a / 2 ^ k) 2
  rw [Nat.div_div_eq_div_mul, ← pow_succ] at he
  exact he.symm

theorem split (a w : ℕ) : a = low a w + 2 ^ w * (a / 2 ^ w) := by
  induction w with
  | zero => simp [low]
  | succ w ih =>
    calc
      a = low a w + 2 ^ w * (a / 2 ^ w) := ih
      _ = low a (w + 1) + 2 ^ (w + 1) * (a / 2 ^ (w + 1)) := by
        rw [div_step a w]
        simp only [low, Finset.sum_range_succ, pow_succ]
        ring

theorem low_mod (a w : ℕ) : low a w % 2 ^ w = a % 2 ^ w := by
  have he := congrArg (fun n => n % 2 ^ w) (split a w)
  simpa only [Nat.add_mul_mod_self_left] using he.symm

theorem sum_term (a b w : ℕ) : (∑ i ∈ Finset.range w, term a b i) = low a w * b := by
  unfold low
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [term, BinarySum.bit_eq]
  cases a.testBit i <;> simp [mul_comm]

theorem term_bit (a b i k : ℕ) :
    (term a b i).testBit k = (a.testBit i && decide (i ≤ k) && b.testBit (k - i)) := by
  unfold term
  cases a.testBit i <;> simp [Nat.testBit_mul_two_pow]

theorem product_bit (a b k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), term a b i).testBit k = (a * b).testBit k := by
  have he : (∑ i ∈ Finset.range (k + 1), term a b i) % 2 ^ (k + 1) = (a * b) % 2 ^ (k + 1) := by
    rw [sum_term, Nat.mul_mod, low_mod, ← Nat.mul_mod]
  have hb := congrArg (fun n => n.testBit k) he
  simpa only [Nat.testBit_mod_two_pow, Nat.lt_add_one, decide_true, Bool.true_and] using hb

end LeanCanny.Algebra.BinaryProduct
