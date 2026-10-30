/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.OrderedRealCellRank

/-! # Refined adjacent gaps stay in the original endpoint gap -/

@[expose] public section
namespace LeanCanny.Geometry.OrderedRealCells
open Set
open scoped Classical

theorem rightGap_refines (s t : Finset ℝ) (hst : s ⊆ t) (i : Fin s.card) (j : Fin t.card)
    (he : root s i = root t j) : gap t (rightGap t j) ⊆ gap s (rightGap s i) := by
  intro x hx
  apply (mem_gap_iff s (rightGap s i) x).mpr
  intro k
  split_ifs with hk
  · have hki : k ≤ i := by change k.val ≤ i.val; change k.val < i.val + 1 at hk; omega
    calc
      root s k ≤ root s i := (root_strictMono s).monotone hki
      _ = root t j := he
      _ < x := root_lt_of_mem_rightGap t j hx
  · have hik : i < k := by change i.val < k.val; change ¬k.val < i.val + 1 at hk; omega
    obtain ⟨l, hl⟩ := exists_root t (root s k) (hst (root_mem s k))
    have hjl : j < l := (root_strictMono t).lt_iff_lt.mp (by rw [← he, hl]; exact root_strictMono s hik)
    have hn : ¬l.val < (rightGap t j).val := by change ¬l.val < j.val + 1; change j.val < l.val at hjl; omega
    have H := (mem_gap_iff t (rightGap t j) x).mp hx l
    rw [ite_eq_right hn, hl] at H
    exact H

theorem leftGap_refines (s t : Finset ℝ) (hst : s ⊆ t) (i : Fin s.card) (j : Fin t.card)
    (he : root s i = root t j) : gap t (leftGap t j) ⊆ gap s (leftGap s i) := by
  intro x hx
  apply (mem_gap_iff s (leftGap s i) x).mpr
  intro k
  split_ifs with hk
  · have hki : k < i := by change k.val < i.val; exact hk
    obtain ⟨l, hl⟩ := exists_root t (root s k) (hst (root_mem s k))
    have hlj : l < j := (root_strictMono t).lt_iff_lt.mp (by rw [← he, hl]; exact root_strictMono s hki)
    have hn : l.val < (leftGap t j).val := hlj
    have H := (mem_gap_iff t (leftGap t j) x).mp hx l
    rw [ite_eq_left hn, hl] at H
    exact H
  · have hik : i ≤ k := by change i.val ≤ k.val; change ¬k.val < i.val at hk; omega
    calc
      x < root t j := lt_root_of_mem_leftGap t j hx
      _ = root s i := he.symm
      _ ≤ root s k := (root_strictMono s).monotone hik

theorem same_gap_eq (s : Finset ℝ) (i j : Fin (s.card + 1)) {x : ℝ}
    (hi : x ∈ gap s i) (hj : x ∈ gap s j) : i = j :=
  Fin.ext ((gap_rank s i x hi).symm.trans (gap_rank s j x hj))

end LeanCanny.Geometry.OrderedRealCells
