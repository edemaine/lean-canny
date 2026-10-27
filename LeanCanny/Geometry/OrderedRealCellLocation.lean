/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.OrderedRealCells

/-! # Locating a real point by root counts

The number of roots strictly below a point gives its root ordinal when it is
a root, and its gap ordinal otherwise. This includes both rays and no roots.
-/

@[expose] public section
namespace LeanCanny.Geometry.OrderedRealCells
open Set
open scoped Classical

noncomputable def lowerCount (s : Finset ℝ) (a : ℝ) : ℕ := (s.filter (fun r => r < a)).card

theorem gap_rank (s : Finset ℝ) (k : Fin (s.card + 1)) (a : ℝ) (ha : a ∈ gap s k) :
    lowerCount s a = k.val := by
  have hc : lowerCount s a ≤ s.card := Finset.card_filter_le _ _
  have hk : k.val ≤ s.card := by have := k.isLt; omega
  have H (j : Fin s.card) : j.val < k.val ↔ j.val < lowerCount s a := by
    rw [lowerCount, ← root_lt_iff]
    have hj := (mem_gap_iff s k a).mp ha j
    by_cases h : j.val < k.val
    · exact ⟨fun _ => by simpa only [h, ite_true] using hj, fun _ => h⟩
    · have hj' : a < root s j := by simpa only [h, ite_false] using hj
      exact ⟨fun he => (h he).elim, fun he => (lt_asymm he hj').elim⟩
  apply Nat.le_antisymm
  · by_contra h
    have hl : k.val < lowerCount s a := by omega
    have hb : k.val < s.card := hl.trans_le hc
    exact (Nat.lt_irrefl k.val) ((H ⟨k.val, hb⟩).mpr hl)
  · by_contra h
    have hl : lowerCount s a < k.val := by omega
    have hb : lowerCount s a < s.card := hl.trans_le hk
    exact (Nat.lt_irrefl (lowerCount s a)) ((H ⟨lowerCount s a, hb⟩).mp hl)

theorem code_of_mem_piece (s : Finset ℝ) (a : ℝ) (i : Index s) (ha : a ∈ piece s i) :
    code s i = if a ∈ s then lowerCount s a else s.card + lowerCount s a := by
  cases i with
  | inl i =>
    change a ∈ ({root s i} : Set ℝ) at ha
    have he : a = root s i := ha
    rw [he, ite_eq_left (root_mem s i)]
    exact root_rank s i
  | inr k =>
    have hn : a ∉ s := gap_no_root s k ha
    rw [ite_eq_right hn, gap_rank s k a ha]
    rfl

end LeanCanny.Geometry.OrderedRealCells
