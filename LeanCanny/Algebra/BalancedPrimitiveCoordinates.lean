/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedPrimitiveTree

/-! # Indexed leaf recovery from balanced primitive parameters

Coordinates here are nested explicit rational pair evaluations. Flattening
them into one numerator/denominator pair per leaf is a separate construction.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedPrimitiveTree
open Polynomial

def coordinate {L : Type*} : (h : ℕ) → Values L h → ℕ → L
  | 0, x, _ => x
  | h + 1, x, j => if j < 2 ^ h then coordinate h x.1 j else coordinate h x.2 (j - 2 ^ h)

variable {L : Type*} [Field L] [CharZero L]

omit [CharZero L] in
theorem valid_iff (a : ℕ → SeparableIntegerPolynomial) (h i : ℕ) (x : Values L h) :
    valid a h i x ↔ ∀ j < 2 ^ h,
      (a (2 ^ h * i + j)).polynomial.eval₂ (Int.castRingHom L) (coordinate h x j) = 0 := by
  induction h generalizing i with
  | zero =>
    constructor
    · intro hx j hj
      have hj' : j = 0 := by simp only [pow_zero] at hj; omega
      simpa only [pow_zero, one_mul, hj', Nat.add_zero, coordinate, valid] using hx
    · intro hx
      simpa only [pow_zero, one_mul, Nat.add_zero, coordinate, valid] using hx 0 (by decide)
  | succ h ih =>
    have hlbase : 2 ^ h * (2 * i) = 2 ^ (h + 1) * i := by rw [pow_succ]; ring
    have hrbase : 2 ^ h * (2 * i + 1) = 2 ^ (h + 1) * i + 2 ^ h := by rw [pow_succ]; ring
    rw [valid, ih, ih]
    constructor
    · rintro ⟨hl, hr⟩ j hj
      by_cases hjl : j < 2 ^ h
      · simpa only [coordinate, ite_eq_left hjl, hlbase] using hl j hjl
      · have hjr : j - 2 ^ h < 2 ^ h := by rw [pow_succ] at hj; omega
        have haddr : 2 ^ h * (2 * i + 1) + (j - 2 ^ h) = 2 ^ (h + 1) * i + j := by rw [hrbase]; omega
        simpa only [coordinate, ite_eq_right hjl, haddr] using hr (j - 2 ^ h) hjr
    · intro hx
      constructor
      · intro j hj
        have hj' : j < 2 ^ (h + 1) := by rw [pow_succ]; omega
        simpa only [coordinate, ite_eq_left hj, hlbase] using hx j hj'
      · intro j hj
        have hj' : 2 ^ h + j < 2 ^ (h + 1) := by rw [pow_succ]; omega
        have hjn : ¬ 2 ^ h + j < 2 ^ h := by omega
        have haddr : 2 ^ (h + 1) * i + (2 ^ h + j) = 2 ^ h * (2 * i + 1) + j := by rw [hrbase]; omega
        simpa only [coordinate, ite_eq_right hjn, Nat.add_sub_cancel_left, haddr] using hx (2 ^ h + j) hj'

theorem decode_coordinate (a : ℕ → SeparableIntegerPolynomial) (h i : ℕ) (theta : L)
    (ht : (node a h i).polynomial.eval₂ (Int.castRingHom L) theta = 0) (j : ℕ) (hj : j < 2 ^ h) :
    (a (2 ^ h * i + j)).polynomial.eval₂ (Int.castRingHom L) (coordinate h (decode a h i theta) j) = 0 :=
  (valid_iff a h i _).mp (decode_root a h i theta ht).1 j hj

end LeanCanny.Algebra.BalancedPrimitiveTree
