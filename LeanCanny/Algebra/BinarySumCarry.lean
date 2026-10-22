/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Bits
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-!
# Reading a sum one binary column at a time

The summands may be exponentially long. At column `k`, sum their selected bits
and the carry from the previous column. Division by two gives the next carry;
parity gives the selected bit of the complete sum. The carry is at most the
number of summands, and a partially accumulated column is at most twice that
number. Only the column/index counters and this short accumulator need storage.
-/

@[expose] public section

namespace LeanCanny.Algebra.BinarySum

open scoped BigOperators

def bit (a k : ℕ) : ℕ := a / 2 ^ k % 2

def column (N : ℕ) (a : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.range N, bit (a i) k

def high (N : ℕ) (a : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.range N, a i / 2 ^ k

def carry (N : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (carry N a k + column N a k) / 2

def partialColumn (N : ℕ) (a : ℕ → ℕ) (k i : ℕ) : ℕ := carry N a k + column i a k

theorem bit_le_one (a k : ℕ) : bit a k ≤ 1 := by
  have := Nat.mod_lt (a / 2 ^ k) (by decide : 0 < 2)
  dsimp only [bit]
  omega

theorem bit_eq (a k : ℕ) : bit a k = if a.testBit k then 1 else 0 := by
  have hsmall := bit_le_one a k
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change bit a k = if decide (bit a k = 1) then 1 else 0
  have hc : bit a k = 0 ∨ bit a k = 1 := by omega
  rcases hc with h | h <;> simp [h]

theorem column_le (N : ℕ) (a : ℕ → ℕ) (k : ℕ) : column N a k ≤ N := by
  calc
    _ ≤ ∑ _i ∈ Finset.range N, 1 := Finset.sum_le_sum (fun i _ => bit_le_one _ _)
    _ = _ := by simp

theorem carry_le (N : ℕ) (a : ℕ → ℕ) (k : ℕ) : carry N a k ≤ N := by
  induction k with
  | zero => simp [carry]
  | succ k ih =>
    have hc := column_le N a k
    simp only [carry]
    omega

theorem partialColumn_le (N : ℕ) (a : ℕ → ℕ) (k i : ℕ) (hi : i ≤ N) : partialColumn N a k i ≤ 2 * N := by
  have := carry_le N a k
  have := column_le i a k
  dsimp only [partialColumn]
  omega

theorem high_step (N : ℕ) (a : ℕ → ℕ) (k : ℕ) :
    high N a k = column N a k + 2 * high N a (k + 1) := by
  simp only [high, column, bit, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mod_add_div _ _ |>.symm

theorem carry_add_high (N : ℕ) (a : ℕ → ℕ) (k : ℕ) :
    carry N a k + high N a k = (∑ i ∈ Finset.range N, a i) / 2 ^ k := by
  induction k with
  | zero => simp [carry, high]
  | succ k ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ← ih, high_step N a k, carry]
    rw [← Nat.add_assoc, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]

theorem sum_testBit (N : ℕ) (a : ℕ → ℕ) (k : ℕ) :
    (∑ i ∈ Finset.range N, a i).testBit k = decide ((carry N a k + column N a k) % 2 = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, ← carry_add_high N a k, high_step N a k]
  have hm : (carry N a k + (column N a k + 2 * high N a (k + 1))) % 2 =
      (carry N a k + column N a k) % 2 := by omega
  rw [hm]

@[simp] theorem partialColumn_zero (N : ℕ) (a : ℕ → ℕ) (k : ℕ) : partialColumn N a k 0 = carry N a k := by
  simp [partialColumn, column]

theorem partialColumn_succ (N : ℕ) (a : ℕ → ℕ) (k i : ℕ) :
    partialColumn N a k (i + 1) = partialColumn N a k i + bit (a i) k := by
  simp only [partialColumn, column, Finset.sum_range_succ]
  omega

theorem partialColumn_next (N : ℕ) (a : ℕ → ℕ) (k : ℕ) :
    partialColumn N a (k + 1) 0 = partialColumn N a k N / 2 := by
  rw [partialColumn_zero]
  rfl

def carryValue (N : ℕ) (a : ℕ → ℕ) (t : ℕ) : ℕ :=
  partialColumn N a (t / (N + 1)) (t % (N + 1))

@[simp] theorem carryValue_zero (N : ℕ) (a : ℕ → ℕ) : carryValue N a 0 = 0 := by
  simp [carryValue, carry]

theorem carryValue_le (N : ℕ) (a : ℕ → ℕ) (t : ℕ) : carryValue N a t ≤ 2 * N :=
  partialColumn_le N a _ _ (by have := Nat.mod_lt t (by omega : 0 < N + 1); omega)

theorem next_coordinates_bit (N t : ℕ) (hi : t % (N + 1) < N) :
    (t + 1) / (N + 1) = t / (N + 1) ∧ (t + 1) % (N + 1) = t % (N + 1) + 1 := by
  have he : t + 1 = (t % (N + 1) + 1) + (N + 1) * (t / (N + 1)) := by
    have := Nat.mod_add_div t (N + 1)
    omega
  rw [he, Nat.add_mul_div_left _ _ (by omega : 0 < N + 1), Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt (by omega : t % (N + 1) + 1 < N + 1),
    Nat.mod_eq_of_lt (by omega : t % (N + 1) + 1 < N + 1), Nat.zero_add]
  exact ⟨rfl, rfl⟩

theorem next_coordinates_carry (N t : ℕ) (hi : ¬ t % (N + 1) < N) :
    (t + 1) / (N + 1) = t / (N + 1) + 1 ∧ (t + 1) % (N + 1) = 0 := by
  have hr := Nat.mod_lt t (by omega : 0 < N + 1)
  have he : t + 1 = (N + 1) * (t / (N + 1) + 1) := by
    have := Nat.mod_add_div t (N + 1)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [he, Nat.mul_div_cancel_left _ (by omega : 0 < N + 1), Nat.mul_mod_right]
  exact ⟨rfl, rfl⟩

theorem carryValue_succ_bit (N : ℕ) (a : ℕ → ℕ) (t : ℕ) (hi : t % (N + 1) < N) :
    carryValue N a (t + 1) = carryValue N a t + bit (a (t % (N + 1))) (t / (N + 1)) := by
  simp only [carryValue, (next_coordinates_bit N t hi).1, (next_coordinates_bit N t hi).2,
    partialColumn_succ]

theorem carryValue_succ_carry (N : ℕ) (a : ℕ → ℕ) (t : ℕ) (hi : ¬ t % (N + 1) < N) :
    carryValue N a (t + 1) = carryValue N a t / 2 := by
  have hr : t % (N + 1) = N := by have := Nat.mod_lt t (by omega : 0 < N + 1); omega
  simp only [carryValue, (next_coordinates_carry N t hi).1, (next_coordinates_carry N t hi).2,
    partialColumn_next, hr]

theorem carryValue_end (N : ℕ) (a : ℕ → ℕ) (K : ℕ) :
    carryValue N a (K * (N + 1) + N) = partialColumn N a K N := by
  rw [carryValue, Nat.mul_comm K, Nat.add_comm ((N + 1) * K),
    Nat.add_mul_div_left _ _ (by omega : 0 < N + 1), Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt (by omega : N < N + 1), Nat.mod_eq_of_lt (by omega : N < N + 1), Nat.zero_add]

end LeanCanny.Algebra.BinarySum
