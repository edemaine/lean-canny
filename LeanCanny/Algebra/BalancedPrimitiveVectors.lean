/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedPrimitiveCoordinates

/-! # Tabulating and comparing the leaf values of a balanced primitive tree -/

@[expose] public section

namespace LeanCanny.Algebra.BalancedPrimitiveTree

def tabulate {L : Type*} : (h : ℕ) → (ℕ → L) → Values L h
  | 0, f => f 0
  | h + 1, f => (tabulate h f, tabulate h (fun j => f (2 ^ h + j)))

theorem coordinate_tabulate {L : Type*} (h : ℕ) (f : ℕ → L) (j : ℕ) (hj : j < 2 ^ h) :
    coordinate h (tabulate h f) j = f j := by
  induction h generalizing f j with
  | zero => have : j = 0 := by simp only [pow_zero] at hj; omega
            subst j; rfl
  | succ h ih =>
    simp only [tabulate, coordinate]
    by_cases hjl : j < 2 ^ h
    · rw [ite_eq_left hjl, ih f j hjl]
    · rw [ite_eq_right hjl, ih _ _ (by rw [pow_succ] at hj; omega)]
      congr 1
      omega

theorem coordinate_injective {L : Type*} (h : ℕ) (x y : Values L h)
    (he : ∀ j < 2 ^ h, coordinate h x j = coordinate h y j) : x = y := by
  induction h with
  | zero => exact he 0 (by decide)
  | succ h ih =>
    apply Prod.ext
    · apply ih x.1 y.1
      intro j hj
      have hj' : j < 2 ^ (h + 1) := by rw [pow_succ]; omega
      simpa only [coordinate, ite_eq_left hj] using he j hj'
    · apply ih x.2 y.2
      intro j hj
      have hj' : 2 ^ h + j < 2 ^ (h + 1) := by rw [pow_succ]; omega
      have hn : ¬ 2 ^ h + j < 2 ^ h := by omega
      simpa only [coordinate, ite_eq_right hn, Nat.add_sub_cancel_left] using he (2 ^ h + j) hj'

end LeanCanny.Algebra.BalancedPrimitiveTree
