/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.OrderedRealCells

/-! # Adjacent gaps approach their retained endpoints

A point in either gap adjacent to a retained root determines a root-free
interval ending at that root. Such points exist inside every prescribed
one-sided neighborhood. Refining a root set therefore preserves access to
each original endpoint, including the first and last retained roots.
-/

@[expose] public section
namespace LeanCanny.Geometry.OrderedRealCells
open Set
open scoped Classical

def rightGap (s : Finset ℝ) (i : Fin s.card) : Fin (s.card + 1) :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

def leftGap (s : Finset ℝ) (i : Fin s.card) : Fin (s.card + 1) :=
  ⟨i.val, by have := i.isLt; omega⟩

theorem root_lt_of_mem_rightGap (s : Finset ℝ) (i : Fin s.card) {t : ℝ}
    (ht : t ∈ gap s (rightGap s i)) : root s i < t := by
  simpa only [rightGap, Nat.lt_succ_self, ite_true] using (mem_gap_iff s (rightGap s i) t).mp ht i

theorem lt_root_of_mem_leftGap (s : Finset ℝ) (i : Fin s.card) {t : ℝ}
    (ht : t ∈ gap s (leftGap s i)) : t < root s i := by
  simpa only [leftGap, lt_self_iff_false, ite_false] using (mem_gap_iff s (leftGap s i) t).mp ht i

theorem right_interval_subset (s : Finset ℝ) (i : Fin s.card) {t : ℝ}
    (ht : t ∈ gap s (rightGap s i)) : Ioo (root s i) t ⊆ gap s (rightGap s i) := by
  intro x hx
  apply (mem_gap_iff s (rightGap s i) x).mpr
  intro j
  split_ifs with hj
  · have hji : j ≤ i := by change j.val ≤ i.val; change j.val < i.val + 1 at hj; omega
    exact ((root_strictMono s).monotone hji).trans_lt hx.1
  · have h := (mem_gap_iff s (rightGap s i) t).mp ht j
    rw [ite_eq_right hj] at h
    exact hx.2.trans h

theorem left_interval_subset (s : Finset ℝ) (i : Fin s.card) {t : ℝ}
    (ht : t ∈ gap s (leftGap s i)) : Ioo t (root s i) ⊆ gap s (leftGap s i) := by
  intro x hx
  apply (mem_gap_iff s (leftGap s i) x).mpr
  intro j
  split_ifs with hj
  · have h := (mem_gap_iff s (leftGap s i) t).mp ht j
    rw [ite_eq_left hj] at h
    exact h.trans hx.1
  · have hij : i ≤ j := by change i.val ≤ j.val; change ¬j.val < i.val at hj; omega
    exact hx.2.trans_le ((root_strictMono s).monotone hij)

theorem exists_rightGap_before (s : Finset ℝ) (i : Fin s.card) {b : ℝ} (hb : root s i < b) :
    ∃ t ∈ gap s (rightGap s i), t < b := by
  obtain ⟨v, hv⟩ := gap_nonempty s (rightGap s i)
  have ha := root_lt_of_mem_rightGap s i hv
  obtain ⟨t, hat, htv⟩ := exists_between (lt_min ha hb)
  exact ⟨t, right_interval_subset s i hv ⟨hat, htv.trans_le (min_le_left _ _)⟩,
    htv.trans_le (min_le_right _ _)⟩

theorem exists_leftGap_after (s : Finset ℝ) (i : Fin s.card) {a : ℝ} (ha : a < root s i) :
    ∃ t ∈ gap s (leftGap s i), a < t := by
  obtain ⟨v, hv⟩ := gap_nonempty s (leftGap s i)
  have hb := lt_root_of_mem_leftGap s i hv
  obtain ⟨t, hvt, htb⟩ := exists_between (max_lt hb ha)
  exact ⟨t, left_interval_subset s i hv ⟨(le_max_left _ _).trans_lt hvt, htb⟩,
    (le_max_right _ _).trans_lt hvt⟩

theorem exists_rightGap_extension (s : Finset ℝ) (i : Fin s.card) {t b : ℝ}
    (ht : t ∈ gap s (rightGap s i)) (hb : t < b) :
    ∃ c ∈ gap s (rightGap s i), t < c ∧ c < b := by
  have hn := ((gap_open s (rightGap s i)).inter isOpen_Iio).mem_nhds ⟨ht, hb⟩
  obtain ⟨l, u, ⟨hlt, htu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  obtain ⟨c, htc, hcu⟩ := exists_between htu
  have hc := hsub ⟨hlt.trans htc, hcu⟩
  exact ⟨c, hc.1, htc, hc.2⟩

theorem exists_leftGap_extension (s : Finset ℝ) (i : Fin s.card) {a t : ℝ}
    (ht : t ∈ gap s (leftGap s i)) (ha : a < t) :
    ∃ c ∈ gap s (leftGap s i), a < c ∧ c < t := by
  have hn := ((gap_open s (leftGap s i)).inter isOpen_Ioi).mem_nhds ⟨ht, ha⟩
  obtain ⟨l, u, ⟨hlt, htu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  obtain ⟨c, hlc, hct⟩ := exists_between hlt
  have hc := hsub ⟨hlc, hct.trans htu⟩
  exact ⟨c, hc.1, hc.2, hct⟩

end LeanCanny.Geometry.OrderedRealCells
