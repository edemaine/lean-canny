/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Analysis.Convex.PathConnected

/-! # Finite point and gap cells on the real line

A finite ordered set determines one point cell at each element and one gap
at each cut. The two exterior gaps are rays; an empty set has one gap equal
to the whole line. These cells cover every real point, are nonempty, and
contain no omitted root in any gap.
-/

@[expose] public section
namespace LeanCanny.Geometry.OrderedRealCells
open Set
open scoped Classical

noncomputable def root (s : Finset ℝ) (i : Fin s.card) : ℝ := (s.orderIsoOfFin rfl i).val
abbrev Index (s : Finset ℝ) := Fin s.card ⊕ Fin (s.card + 1)

theorem root_mem (s : Finset ℝ) (i : Fin s.card) : root s i ∈ s := (s.orderIsoOfFin rfl i).property
theorem root_strictMono (s : Finset ℝ) : StrictMono (root s) := (s.orderIsoOfFin rfl).strictMono

theorem exists_root (s : Finset ℝ) (x : ℝ) (hx : x ∈ s) : ∃ i, root s i = x := by
  exact ⟨(s.orderIsoOfFin rfl).symm ⟨x, hx⟩, congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)⟩

noncomputable def gap (s : Finset ℝ) (k : Fin (s.card + 1)) : Set ℝ :=
  ⋂ j : Fin s.card, if j.val < k.val then Ioi (root s j) else Iio (root s j)

theorem mem_gap_iff (s : Finset ℝ) (k : Fin (s.card + 1)) (x : ℝ) :
    x ∈ gap s k ↔ ∀ j : Fin s.card, if j.val < k.val then root s j < x else x < root s j := by
  simp only [gap, mem_iInter]
  apply forall_congr'
  intro j
  split_ifs <;> rfl

theorem gap_convex (s : Finset ℝ) (k : Fin (s.card + 1)) : Convex ℝ (gap s k) := by
  apply convex_iInter
  intro j
  split_ifs
  · exact convex_Ioi _
  · exact convex_Iio _

theorem gap_open (s : Finset ℝ) (k : Fin (s.card + 1)) : IsOpen (gap s k) := by
  apply isOpen_iInter_of_finite
  intro j
  split_ifs
  · exact isOpen_Ioi
  · exact isOpen_Iio

theorem gap_no_root (s : Finset ℝ) (k : Fin (s.card + 1)) {x : ℝ} (hx : x ∈ gap s k) : x ∉ s := by
  intro hxs
  obtain ⟨j, hj⟩ := exists_root s x hxs
  have H := (mem_gap_iff s k x).mp hx j
  rw [hj] at H
  split_ifs at H <;> exact (lt_irrefl _) H

theorem gap_empty (k : Fin ((∅ : Finset ℝ).card + 1)) : gap ∅ k = univ := by
  ext x
  rw [mem_gap_iff]
  simp only [mem_univ, iff_true]
  intro j
  exact Fin.elim0 j

theorem gap_zero {s : Finset ℝ} (hs : 0 < s.card) :
    gap s ⟨0, by omega⟩ = Iio (root s ⟨0, hs⟩) := by
  ext x
  rw [mem_gap_iff]
  simp only [Nat.not_lt_zero, ite_false, mem_Iio]
  constructor
  · intro H
    exact H ⟨0, hs⟩
  · intro H j
    exact H.trans_le ((root_strictMono s).monotone (show (⟨0, hs⟩ : Fin s.card) ≤ j from Nat.zero_le _))

theorem gap_last {s : Finset ℝ} (hs : 0 < s.card) :
    gap s ⟨s.card, by omega⟩ = Ioi (root s ⟨s.card - 1, by omega⟩) := by
  ext x
  rw [mem_gap_iff]
  simp only [Fin.isLt, ite_true, mem_Ioi]
  constructor
  · intro H
    exact H ⟨s.card - 1, by omega⟩
  · intro H j
    exact ((root_strictMono s).monotone (show j ≤ ⟨s.card - 1, by omega⟩ from by
      change j.val ≤ s.card - 1; have := j.isLt; omega)).trans_lt H

theorem gap_interior {s : Finset ℝ} (k : Fin (s.card + 1)) (h0 : 0 < k.val) (hk : k.val < s.card) :
    gap s k = Ioo (root s ⟨k.val - 1, by omega⟩) (root s ⟨k.val, hk⟩) := by
  ext x
  rw [mem_gap_iff, mem_Ioo]
  constructor
  · intro H
    have hl := H ⟨k.val - 1, by omega⟩
    have hu := H ⟨k.val, hk⟩
    simp only [show k.val - 1 < k.val from by omega, ite_true] at hl
    simp only [lt_self_iff_false, ite_false] at hu
    exact ⟨hl, hu⟩
  · rintro ⟨hl, hu⟩ j
    split_ifs with hj
    · exact ((root_strictMono s).monotone (show j ≤ ⟨k.val - 1, by omega⟩ from by change j.val ≤ k.val - 1; omega)).trans_lt hl
    · exact hu.trans_le ((root_strictMono s).monotone (show (⟨k.val, hk⟩ : Fin s.card) ≤ j from by change k.val ≤ j.val; omega))

theorem gap_nonempty (s : Finset ℝ) (k : Fin (s.card + 1)) : (gap s k).Nonempty := by
  by_cases hs : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hs
    subst s
    rw [gap_empty]
    exact ⟨0, mem_univ _⟩
  · have hs' : 0 < s.card := by omega
    by_cases hk0 : k.val = 0
    · have hk : k = ⟨0, by omega⟩ := Fin.ext hk0
      rw [hk, gap_zero hs']
      exact ⟨root s ⟨0, hs'⟩ - 1, by simp only [mem_Iio]; linarith⟩
    · by_cases hkN : k.val = s.card
      · have hk : k = ⟨s.card, by omega⟩ := Fin.ext hkN
        rw [hk, gap_last hs']
        exact ⟨root s ⟨s.card - 1, by omega⟩ + 1, by simp only [mem_Ioi]; linarith⟩
      · have hk : k.val < s.card := by have := k.isLt; omega
        have h0 : 0 < k.val := by omega
        rw [gap_interior k h0 hk]
        exact nonempty_Ioo.mpr ((root_strictMono s) (show (⟨k.val - 1, by omega⟩ : Fin s.card) < ⟨k.val, hk⟩ from by
          change k.val - 1 < k.val; omega))

noncomputable def piece (s : Finset ℝ) : Index s → Set ℝ
  | .inl i => {root s i}
  | .inr k => gap s k

theorem piece_nonempty (s : Finset ℝ) (i : Index s) : (piece s i).Nonempty := by
  cases i with
  | inl i => exact singleton_nonempty _
  | inr k => exact gap_nonempty s k

theorem piece_pathConnected (s : Finset ℝ) (i : Index s) : IsPathConnected (piece s i) := by
  cases i with
  | inl i => exact isPathConnected_singleton (root s i)
  | inr k => exact (gap_convex s k).isPathConnected (gap_nonempty s k)

private theorem ordered_rank_eq_card (s : Finset ℝ) (x : {a // a ∈ s}) :
    ((s.orderIsoOfFin rfl).symm x).val = (s.filter (fun a => a < x.val)).card := by
  let e := (s.orderIsoOfFin rfl).symm
  rw [← Finset.card_range (e x).val]
  symm
  apply Finset.card_bij (fun y hy => (e ⟨y, (Finset.mem_filter.mp hy).1⟩).val)
  · intro y hy
    exact Finset.mem_range.mpr (e.lt_iff_lt.mpr (Finset.mem_filter.mp hy).2)
  · intro a ha b hb hab
    exact congrArg Subtype.val (e.injective (Fin.ext hab))
  · intro n hn
    have hn' := Finset.mem_range.mp hn
    let j : Fin s.card := ⟨n, hn'.trans (e x).isLt⟩
    refine ⟨(e.symm j).val, Finset.mem_filter.mpr ⟨(e.symm j).property, ?_⟩, ?_⟩
    · have H := e.symm.strictMono (show j < e x from hn')
      rw [e.symm_apply_apply] at H
      exact H
    · simp only [e.apply_symm_apply]
      rfl

theorem root_rank (s : Finset ℝ) (i : Fin s.card) :
    i.val = (s.filter (fun y => y < root s i)).card := by
  have H := ordered_rank_eq_card s (s.orderIsoOfFin rfl i)
  rw [OrderIso.symm_apply_apply] at H
  exact H

theorem root_lt_iff (s : Finset ℝ) (i : Fin s.card) (x : ℝ) :
    root s i < x ↔ i.val < (s.filter (fun y => y < x)).card := by
  have hr := root_rank s i
  constructor
  · intro hx
    rw [hr]
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun y hy => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2.trans hx⟩, ?_⟩
    intro he
    have H : root s i ∈ s.filter (fun y => y < x) := Finset.mem_filter.mpr ⟨root_mem s i, hx⟩
    rw [← he] at H
    exact (lt_irrefl _) (Finset.mem_filter.mp H).2
  · intro hi
    by_contra hx
    have hs : s.filter (fun y => y < x) ⊆ s.filter (fun y => y < root s i) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2.trans_le (le_of_not_gt hx)⟩
    have H := Finset.card_le_card hs
    omega

theorem cover (s : Finset ℝ) (x : ℝ) : ∃ i : Index s, x ∈ piece s i := by
  by_cases hx : x ∈ s
  · obtain ⟨i, hi⟩ := exists_root s x hx
    exact ⟨.inl i, hi.symm⟩
  · let k : Fin (s.card + 1) := ⟨(s.filter (fun y => y < x)).card, (Finset.card_filter_le s _).trans_lt (Nat.lt_succ_self _)⟩
    refine ⟨.inr k, (mem_gap_iff s k x).mpr ?_⟩
    intro j
    split_ifs with hj
    · exact (root_lt_iff s j x).mpr hj
    · have hjx : ¬root s j < x := (root_lt_iff s j x).not.mpr hj
      have he : x ≠ root s j := fun h => hx (h ▸ root_mem s j)
      exact lt_of_le_of_ne (le_of_not_gt hjx) he

theorem card_index (s : Finset ℝ) : Fintype.card (Index s) = 2 * s.card + 1 := by
  simp only [Index, Fintype.card_sum, Fintype.card_fin]
  omega

def code (s : Finset ℝ) : Index s → ℕ
  | .inl i => i.val
  | .inr k => s.card + k.val

theorem code_lt (s : Finset ℝ) (i : Index s) : code s i < 2 * s.card + 1 := by
  cases i with
  | inl i => have H := i.isLt; change i.val < _; omega
  | inr k => have H := k.isLt; change s.card + k.val < _; omega

theorem code_injective (s : Finset ℝ) : Function.Injective (code s) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (Fin.ext h)
    | inr k => have H := i.isLt; change i.val = s.card + k.val at h; omega
  | inr k =>
    cases j with
    | inl j => have H := j.isLt; change s.card + k.val = j.val at h; omega
    | inr l =>
      apply congrArg Sum.inr
      apply Fin.ext
      change s.card + k.val = s.card + l.val at h
      omega

def decode (s : Finset ℝ) (n : ℕ) (hn : n < 2 * s.card + 1) : Index s :=
  if h : n < s.card then .inl ⟨n, h⟩ else .inr ⟨n - s.card, by omega⟩

theorem code_decode (s : Finset ℝ) (n : ℕ) (hn : n < 2 * s.card + 1) : code s (decode s n hn) = n := by
  unfold decode
  split_ifs with h
  · rfl
  · change s.card + (n - s.card) = n
    omega

end LeanCanny.Geometry.OrderedRealCells
