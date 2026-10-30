/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.OrderedRealCellLocation
public import LeanCanny.Geometry.OrderedRealCellNeighborhood

/-! # Adjacent gap membership from two root ranks

A nonroot is in a retained gap precisely when its lower-root count is the
gap ordinal. Thus two independently represented algebraic points can be
checked for endpoint adjacency by counts alone.
-/

@[expose] public section
namespace LeanCanny.Geometry.OrderedRealCells
open scoped Classical

theorem mem_gap_iff_rank (s : Finset ℝ) (k : Fin (s.card + 1)) (t : ℝ) :
    t ∈ gap s k ↔ t ∉ s ∧ lowerCount s t = k.val := by
  constructor
  · intro ht
    exact ⟨gap_no_root s k ht, gap_rank s k t ht⟩
  · rintro ⟨hn, he⟩
    apply (mem_gap_iff s k t).mpr
    intro j
    split_ifs with hj
    · have hj' : j.val < lowerCount s t := by omega
      exact (root_lt_iff s j t).mpr hj'
    · have hj' : ¬j.val < lowerCount s t := by omega
      have hnot : ¬root s j < t := (root_lt_iff s j t).not.mpr hj'
      have hne : t ≠ root s j := fun h => hn (h ▸ root_mem s j)
      exact lt_of_le_of_ne (le_of_not_gt hnot) hne

theorem mem_rightGap_iff_rank (s : Finset ℝ) (i : Fin s.card) (t : ℝ) :
    t ∈ gap s (rightGap s i) ↔ t ∉ s ∧ lowerCount s t = lowerCount s (root s i) + 1 := by
  have hi : lowerCount s (root s i) = i.val := (root_rank s i).symm
  rw [mem_gap_iff_rank, hi]
  rfl

theorem mem_leftGap_iff_rank (s : Finset ℝ) (i : Fin s.card) (t : ℝ) :
    t ∈ gap s (leftGap s i) ↔ t ∉ s ∧ lowerCount s t = lowerCount s (root s i) := by
  have hi : lowerCount s (root s i) = i.val := (root_rank s i).symm
  rw [mem_gap_iff_rank, hi]
  rfl

end LeanCanny.Geometry.OrderedRealCells
