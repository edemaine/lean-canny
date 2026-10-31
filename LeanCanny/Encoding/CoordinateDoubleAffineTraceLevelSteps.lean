/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceLevels

/-! # Appending history reproduces the fixed-height and midpoint level rules -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
set_option backward.isDefEq.respectTransparency false

theorem levelAt_depth_frozen (n d c : ℕ) (trace : List Bool) (seed : ℕ → ℕ → List Bool) (j : ℕ) :
    FlatAffineFrozenLevelRecord.freeze (d + offset trace) (levelAt n d c trace seed (d + offset trace) j) =
      if c ≤ j ∧ j < c + trace.length then generated n d c trace (min (j - c) trace.length)
      else FlatAffineFrozenLevelRecord.freeze d (seed d j) := by
  by_cases ht : trace = []
  · subst trace
    have hj : ¬ (c ≤ j ∧ j < c) := by omega
    simp [levelAt, offset, completed, hj]
  · rw [levelAt, ite_eq_right (by omega), completed_of_depth_le d trace _ (le_refl _)]
    by_cases hj : c ≤ j ∧ j < c + trace.length
    · rw [ite_eq_left hj, ite_eq_left hj]
      apply freeze_generated
      · omega
      · exact Nat.add_le_add_left (offset_take_le trace _) d
    · rw [ite_eq_right hj, ite_eq_right hj, ite_eq_right ht]
      exact FlatAffineFrozenLevelRecord.freeze_freeze d (d + offset trace) (by omega) _

theorem levelAt_append_before (n d c : ℕ) (trace : List Bool) (seed : ℕ → ℕ → List Bool)
    (midpoint : Bool) (k j : ℕ) (hk : k < d + offset trace) :
    levelAt n d c (trace ++ [midpoint]) seed k j = levelAt n d c trace seed k j := by
  have hc : 0 < CoordinateDoubleAffineChildRecords.copies midpoint := by cases midpoint <;> decide
  have ho := offset_append trace midpoint
  by_cases hd : k < d
  · simp only [levelAt, hd, ↓reduceIte]
  · have ht : trace ≠ [] := by intro h; subst trace; simp [offset] at hk; omega
    have hn : trace ++ [midpoint] ≠ [] := by simp
    have H : completed d (trace ++ [midpoint]) k = completed d trace k := by
      rw [completed_append, ite_eq_right (by omega), Nat.add_zero]
    simp only [levelAt, hd, ↓reduceIte, H, ht, hn]
    split_ifs with hj
    · have hbound := completed_le d trace k
      have hi : j - c < trace.length := by omega
      rw [Nat.min_eq_left (by simp only [List.length_append, List.length_singleton]; omega),
        Nat.min_eq_left hi.le]
      exact generated_append_old n d c trace midpoint (j - c) hi
    · rfl

theorem levelAt_append_after (n d c : ℕ) (trace : List Bool) (seed : ℕ → ℕ → List Bool)
    (midpoint : Bool) (k j : ℕ) (hl : d + offset trace ≤ k) (hk : k ≤ d + offset (trace ++ [midpoint])) :
    levelAt n d c (trace ++ [midpoint]) seed k j =
      if k = d + offset (trace ++ [midpoint]) ∧ j = c + trace.length then
        record midpoint n (c + trace.length) (d + offset trace) else
          FlatAffineFrozenLevelRecord.freeze (d + offset trace) (levelAt n d c trace seed (d + offset trace) j) := by
  rw [levelAt_depth_frozen]
  have hd : ¬ k < d := by omega
  have hn : trace ++ [midpoint] ≠ [] := by simp
  rw [levelAt, ite_eq_right hd, ite_eq_right hn]
  have H := completed_append d trace midpoint k
  rw [completed_of_depth_le d trace k hl] at H
  by_cases he : k = d + offset (trace ++ [midpoint]) ∧ j = c + trace.length
  · rw [ite_eq_left he]
    have HC : completed d (trace ++ [midpoint]) k = trace.length + 1 := by
      rw [H, ite_eq_left (by omega)]
    rw [HC, ite_eq_left (by omega)]
    rw [he.2, Nat.add_sub_cancel_left, Nat.min_eq_left (by simp only [List.length_append, List.length_singleton]; omega)]
    exact generated_append_new n d c trace midpoint
  · rw [ite_eq_right he]
    have HB : (c ≤ j ∧ j < c + completed d (trace ++ [midpoint]) k) ↔ (c ≤ j ∧ j < c + trace.length) := by
      split_ifs at H <;> omega
    rw [if_congr HB rfl rfl]
    by_cases hj : c ≤ j ∧ j < c + trace.length
    · rw [ite_eq_left hj, ite_eq_left hj]
      have hi : j - c < trace.length := by omega
      rw [Nat.min_eq_left (by simp only [List.length_append, List.length_singleton]; omega), Nat.min_eq_left hi.le]
      exact generated_append_old n d c trace midpoint (j - c) hi
    · rw [ite_eq_right hj, ite_eq_right hj]

theorem levelAt_append (n d c : ℕ) (trace : List Bool) (seed : ℕ → ℕ → List Bool)
    (midpoint : Bool) (k j : ℕ) (hk : k ≤ d + offset (trace ++ [midpoint])) :
    levelAt n d c (trace ++ [midpoint]) seed k j =
      if k < d + offset trace then levelAt n d c trace seed k j else
        if k = d + offset (trace ++ [midpoint]) ∧ j = c + trace.length then
          record midpoint n (c + trace.length) (d + offset trace) else
            FlatAffineFrozenLevelRecord.freeze (d + offset trace) (levelAt n d c trace seed (d + offset trace) j) := by
  by_cases hl : k < d + offset trace
  · rw [ite_eq_left hl]
    exact levelAt_append_before n d c trace seed midpoint k j hl
  · rw [ite_eq_right hl]
    exact levelAt_append_after n d c trace seed midpoint k j (by omega) hk

end LeanCanny.Encoding.CoordinateDoubleAffineTrace
