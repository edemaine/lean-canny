/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.OrderedRealCellCover

/-! # Exact incidence of point and gap cells

Distinct gaps have no frontier incidence with each other. A point cell meets
the closure of a gap exactly at one of the two neighboring cuts. Thus cell
incidence is determined by finite index comparisons, including exterior rays.
-/

@[expose] public section
namespace LeanCanny.Connectivity.OrderedRealCellIncidence
open Set Geometry.OrderedRealCells
open scoped Classical

theorem root_mem_closure_gap (s : Finset ℝ) (i : Fin s.card) (k : Fin (s.card + 1)) :
    root s i ∈ closure (gap s k) ↔ k.val = i.val ∨ k.val = i.val + 1 := by
  have hs : 0 < s.card := Nat.zero_lt_of_lt i.isLt
  by_cases hk0 : k.val = 0
  · have hk : k = ⟨0, by omega⟩ := Fin.ext hk0
    rw [hk, gap_zero hs, closure_Iio, mem_Iic, (root_strictMono s).le_iff_le]
    change i.val ≤ 0 ↔ 0 = i.val ∨ 0 = i.val + 1
    omega
  · by_cases hkN : k.val = s.card
    · have hk : k = ⟨s.card, by omega⟩ := Fin.ext hkN
      rw [hk, gap_last hs, closure_Ioi, mem_Ici, (root_strictMono s).le_iff_le]
      change s.card - 1 ≤ i.val ↔ s.card = i.val ∨ s.card = i.val + 1
      have H := i.isLt
      omega
    · have hk : k.val < s.card := by have := k.isLt; omega
      have h0 : 0 < k.val := by omega
      have hroot : root s ⟨k.val - 1, by omega⟩ < root s ⟨k.val, hk⟩ :=
        (root_strictMono s) (by change k.val - 1 < k.val; omega)
      rw [gap_interior k h0 hk, closure_Ioo hroot.ne, mem_Icc,
        (root_strictMono s).le_iff_le, (root_strictMono s).le_iff_le]
      change k.val - 1 ≤ i.val ∧ i.val ≤ k.val ↔ k.val = i.val ∨ k.val = i.val + 1
      omega

theorem closure_gap_bounds (s : Finset ℝ) (k : Fin (s.card + 1)) {x : ℝ} (hx : x ∈ closure (gap s k))
    (j : Fin s.card) : if j.val < k.val then root s j ≤ x else x ≤ root s j := by
  split_ifs with hj
  · apply (closure_minimal (t := Ici (root s j)) ?_ isClosed_Ici) hx
    intro y hy
    have H := (mem_gap_iff s k y).mp hy j
    rw [ite_eq_left hj] at H
    exact H.le
  · apply (closure_minimal (t := Iic (root s j)) ?_ isClosed_Iic) hx
    intro y hy
    have H := (mem_gap_iff s k y).mp hy j
    rw [ite_eq_right hj] at H
    exact H.le

theorem gap_meets_closure_gap (s : Finset ℝ) (k l : Fin (s.card + 1)) {x : ℝ}
    (hx : x ∈ gap s k) (hy : x ∈ closure (gap s l)) : k = l := by
  apply Fin.ext
  by_contra h
  by_cases hkl : k.val < l.val
  · let j : Fin s.card := ⟨k.val, hkl.trans_le (Nat.le_of_lt_succ l.isLt)⟩
    have H := (mem_gap_iff s k x).mp hx j
    have J := closure_gap_bounds s l hy j
    simp only [j, lt_self_iff_false, ite_false] at H
    simp only [j, hkl, ite_true] at J
    exact (not_lt_of_ge J) H
  · have hlk : l.val < k.val := by omega
    let j : Fin s.card := ⟨l.val, hlk.trans_le (Nat.le_of_lt_succ k.isLt)⟩
    have H := (mem_gap_iff s k x).mp hx j
    have J := closure_gap_bounds s l hy j
    simp only [j, hlk, ite_true] at H
    simp only [j, lt_self_iff_false, ite_false] at J
    exact (not_lt_of_ge J) H

def Adjacent (s : Finset ℝ) : Index s → Index s → Prop
  | .inl i, .inl j => i = j
  | .inl i, .inr k => k.val = i.val ∨ k.val = i.val + 1
  | .inr k, .inl i => k.val = i.val ∨ k.val = i.val + 1
  | .inr k, .inr l => k = l

theorem incident_self (s : Finset ℝ) (i : Index s) : FrontierCover.Incident (piece s) i i := by
  obtain ⟨x, hx⟩ := piece_nonempty s i
  exact Or.inl ⟨x, hx, subset_closure hx⟩

theorem point_point (s : Finset ℝ) (i j : Fin s.card) :
    FrontierCover.Incident (piece s) (.inl i) (.inl j) ↔ i = j := by
  constructor
  · rintro (⟨x, hx, hy⟩ | ⟨x, hy, hx⟩)
    · simp only [piece, closure_singleton, mem_singleton_iff] at hx hy
      exact (root_strictMono s).injective (hx.symm.trans hy)
    · simp only [piece, closure_singleton, mem_singleton_iff] at hx hy
      exact (root_strictMono s).injective (hx.symm.trans hy)
  · rintro rfl
    exact incident_self s _

theorem point_gap (s : Finset ℝ) (i : Fin s.card) (k : Fin (s.card + 1)) :
    FrontierCover.Incident (piece s) (.inl i) (.inr k) ↔ k.val = i.val ∨ k.val = i.val + 1 := by
  constructor
  · rintro (⟨x, hx, hy⟩ | ⟨x, hx, hy⟩)
    · change x = root s i at hx
      subst x
      exact (root_mem_closure_gap s i k).mp hy
    · have he : x = root s i := by simpa only [piece, closure_singleton, mem_singleton_iff] using hy
      subst x
      exact False.elim (gap_no_root s k hx (root_mem s i))
  · intro h
    exact Or.inl ⟨root s i, rfl, (root_mem_closure_gap s i k).mpr h⟩

theorem gap_gap (s : Finset ℝ) (k l : Fin (s.card + 1)) :
    FrontierCover.Incident (piece s) (.inr k) (.inr l) ↔ k = l := by
  constructor
  · rintro (⟨x, hx, hy⟩ | ⟨x, hx, hy⟩)
    · exact gap_meets_closure_gap s k l hx hy
    · exact (gap_meets_closure_gap s l k hx hy).symm
  · rintro rfl
    exact incident_self s _

theorem incident_iff_adjacent (s : Finset ℝ) (i j : Index s) :
    FrontierCover.Incident (piece s) i j ↔ Adjacent s i j := by
  cases i with
  | inl i =>
    cases j with
    | inl j => exact point_point s i j
    | inr k => exact point_gap s i k
  | inr k =>
    cases j with
    | inl i => exact (FrontierCover.incident_symm (piece s)).trans (point_gap s i k)
    | inr l => exact gap_gap s k l

def CodeAdjacent (n a b : ℕ) : Prop := a = b ∨
  (a < n ∧ n ≤ b ∧ (b = n + a ∨ b = n + a + 1)) ∨
  (b < n ∧ n ≤ a ∧ (a = n + b ∨ a = n + b + 1))

theorem code_adjacent_iff (s : Finset ℝ) (i j : Index s) :
    CodeAdjacent s.card (code s i) (code s j) ↔ Adjacent s i j := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [CodeAdjacent, code, Adjacent]
      have hi := i.isLt
      have hj := j.isLt
      rw [Fin.ext_iff]
      omega
    | inr k =>
      simp only [CodeAdjacent, code, Adjacent]
      have hi := i.isLt
      omega
  | inr k =>
    cases j with
    | inl i =>
      simp only [CodeAdjacent, code, Adjacent]
      have hi := i.isLt
      omega
    | inr l =>
      simp only [CodeAdjacent, code, Adjacent]
      rw [Fin.ext_iff]
      omega

end LeanCanny.Connectivity.OrderedRealCellIncidence
