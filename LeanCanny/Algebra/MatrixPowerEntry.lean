/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Balanced recursion for a matrix-power entry

At height `h`, an entry of `A^e` is split into entries of the powers with
exponents `e/2` and `e-e/2`. The result is correct whenever `e ≤ 2^h`.
Consequently the binary length of `e` supplies sufficient height. The matrix
is an entry function; none of its intermediate powers is stored.

`entry` specifies the recursive sums. The continuation machine in
`MatrixPowerMachine` streams those sums. The work recurrence counts that
machine's transitions, rather than assigning unit cost to an entire sum.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower

variable {R : Type*} [Semiring R] {n : ℕ}

def entry (A : Matrix (Fin n) (Fin n) R) : ℕ → ℕ → Fin n → Fin n → R
  | 0, e, i, j => if e = 0 then if i = j then 1 else 0 else if e = 1 then A i j else 0
  | h + 1, e, i, j =>
      if e = 0 then if i = j then 1 else 0
      else if e = 1 then A i j
      else ∑ k, entry A h (e / 2) i k * entry A h (e - e / 2) k j

theorem entry_eq_pow (A : Matrix (Fin n) (Fin n) R) (h e : ℕ)
    (he : e ≤ 2 ^ h) (i j : Fin n) : entry A h e i j = (A ^ e) i j := by
  induction h generalizing e i j with
  | zero =>
      have : e = 0 ∨ e = 1 := by simp only [pow_zero] at he; omega
      rcases this with rfl | rfl <;> simp [entry, Matrix.one_apply]
  | succ h ih =>
      by_cases hzero : e = 0
      · subst e; simp [entry, Matrix.one_apply]
      by_cases hone : e = 1
      · subst e; simp [entry]
      have hhalf : e / 2 ≤ 2 ^ h := by rw [pow_succ] at he; omega
      have hrest : e - e / 2 ≤ 2 ^ h := by rw [pow_succ] at he; omega
      simp only [entry, hzero, hone, ↓reduceIte]
      simp_rw [ih _ hhalf, ih _ hrest]
      rw [← Matrix.mul_apply, ← pow_add, Nat.add_sub_of_le (Nat.div_le_self e 2)]

theorem entry_size_eq_pow (A : Matrix (Fin n) (Fin n) R) (e : ℕ) (i j : Fin n) :
    entry A e.size e i j = (A ^ e) i j :=
  entry_eq_pow A e.size e (Nat.lt_size_self e).le i j

/-- Exact transition count from evaluating a query to returning its scalar.
The continuation after that return is not included. -/
def work (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | h + 1, e =>
      if e ≤ 1 then 1
      else 1 + n * (work n h (e / 2) + work n h (e - e / 2) + 2)

theorem work_pos (n h e : ℕ) : 0 < work n h e := by
  cases h <;> simp only [work]
  · decide
  · split_ifs <;> omega

theorem work_le (n h e : ℕ) : work n h e ≤ (4 * n + 1) ^ h := by
  induction h generalizing e with
  | zero => simp [work]
  | succ h ih =>
      have hpos : 0 < (4 * n + 1) ^ h := pow_pos (by omega) _
      rw [work, pow_succ]
      split_ifs
      · nlinarith
      · have hl := ih (e / 2)
        have hr := ih (e - e / 2)
        nlinarith

theorem work_add_one_le_two_pow (n h e : ℕ) :
    work n h e + 1 ≤ 2 ^ ((n.size + 2) * h + 1) := by
  have hbase : 4 * n + 1 ≤ 2 ^ (n.size + 2) := by
    have hn := Nat.lt_size_self n
    calc
      _ ≤ 4 * 2 ^ n.size := by omega
      _ = _ := by rw [pow_add]; norm_num; exact Nat.mul_comm _ _
  have hw : work n h e ≤ 2 ^ ((n.size + 2) * h) :=
    (work_le n h e).trans
      ((Nat.pow_le_pow_left hbase h).trans_eq (pow_mul _ _ _).symm)
  have hp : 0 < 2 ^ ((n.size + 2) * h) := pow_pos (by decide) _
  rw [pow_succ]
  omega

end LeanCanny.Algebra.MatrixPower
