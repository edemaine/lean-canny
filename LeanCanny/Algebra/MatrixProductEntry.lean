/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerEntry
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Balanced access to an ordered matrix product

A matrix family is accessed by its natural-number position. A product interval
is represented by its start and length. Balanced entry recursion splits the
interval in half, preserving factor order and needing only the binary length
of the interval as recursion height. Finite sums here are mathematical
specifications. `LayeredMatrixMachine` reduces this ordered product to the
existing streamed power machine, with factor-access costs still explicit.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixProduct

variable {R : Type*} [Semiring R] {n : ℕ}

def product (A : ℕ → Matrix (Fin n) (Fin n) R) (s : ℕ) : ℕ → Matrix (Fin n) (Fin n) R
  | 0 => 1
  | e + 1 => A s * product A (s + 1) e

theorem product_add (A : ℕ → Matrix (Fin n) (Fin n) R) (s a b : ℕ) :
    product A s (a + b) = product A s a * product A (s + a) b := by
  induction a generalizing s with
  | zero => simp [product]
  | succ a ih =>
      simp only [Nat.succ_add, product]
      rw [ih]
      simp only [Matrix.mul_assoc, Nat.add_comm, Nat.add_left_comm]

theorem product_congr (A B : ℕ → Matrix (Fin n) (Fin n) R) (s t e : ℕ)
    (hab : ∀ k, k < e → A (s + k) = B (t + k)) : product A s e = product B t e := by
  induction e generalizing s t with
  | zero => rfl
  | succ e ih =>
      have hzero := hab 0 (by omega)
      simp only [Nat.add_zero] at hzero
      rw [product, product, hzero]
      congr 1
      apply ih
      intro k hk
      have h := hab (k + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem product_getD (L : List (Matrix (Fin n) (Fin n) R)) :
    product (fun k => L[k]?.getD 1) 0 L.length = L.prod := by
  induction L with
  | nil => rfl
  | cons B L ih =>
      rw [List.length_cons, product]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      have h : product (fun k => (B :: L)[k]?.getD 1) 1 L.length =
          product (fun k => L[k]?.getD 1) 0 L.length := by
        apply product_congr
        intro k _
        simp [Nat.add_comm]
      rw [h, ih, List.prod_cons]

def entry (A : ℕ → Matrix (Fin n) (Fin n) R) : ℕ → ℕ → ℕ → Fin n → Fin n → R
  | 0, s, e, i, j =>
      if e = 0 then if i = j then 1 else 0 else if e = 1 then A s i j else 0
  | h + 1, s, e, i, j =>
      if e = 0 then if i = j then 1 else 0
      else if e = 1 then A s i j
      else ∑ k, entry A h s (e / 2) i k * entry A h (s + e / 2) (e - e / 2) k j

theorem entry_eq_product (A : ℕ → Matrix (Fin n) (Fin n) R) (h s e : ℕ)
    (he : e ≤ 2 ^ h) (i j : Fin n) : entry A h s e i j = product A s e i j := by
  induction h generalizing s e i j with
  | zero =>
      have : e = 0 ∨ e = 1 := by simp only [pow_zero] at he; omega
      rcases this with rfl | rfl <;> simp [entry, product, Matrix.one_apply]
  | succ h ih =>
      by_cases hz : e = 0
      · subst e; simp [entry, product, Matrix.one_apply]
      by_cases ho : e = 1
      · subst e; simp [entry, product]
      have hl : e / 2 ≤ 2 ^ h := by rw [pow_succ] at he; omega
      have hr : e - e / 2 ≤ 2 ^ h := by rw [pow_succ] at he; omega
      simp only [entry, hz, ho, ↓reduceIte]
      simp_rw [ih _ _ hl, ih _ _ hr]
      rw [← Matrix.mul_apply, ← product_add, Nat.add_sub_of_le (Nat.div_le_self e 2)]

theorem entry_size_eq_product (A : ℕ → Matrix (Fin n) (Fin n) R) (s e : ℕ) (i j : Fin n) :
    entry A e.size s e i j = product A s e i j :=
  entry_eq_product A e.size s e (Nat.lt_size_self e).le i j

end LeanCanny.Algebra.MatrixProduct
