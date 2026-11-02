/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.OrderedRealCells
public import Mathlib.Topology.Order.Compact
/-! # Finite sweep cuts retain root origins or empty artificial endpoint fibers -/
@[expose] public section
namespace LeanCanny.Connectivity.FiniteCriticalSweepOrigins
open Set LeanCanny.Geometry
open scoped Classical

theorem exists_cuts {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (p : X → ℝ) (hp : Continuous p) (bad : Set ℝ) (hb : bad.Finite) :
    ∃ n : ℕ, ∃ cut : Fin (n+2) → ℝ, StrictMono cut ∧
      (∀ t ∈ bad, ∃ j, cut j = t) ∧
      (∀ x, p x ∈ Icc (cut 0) (cut (Fin.last (n+1)))) ∧
      (∀ i : Fin (n+1), ∀ t ∈ Ioo (cut i.castSucc) (cut i.succ), t ∉ bad) ∧
      ∀ j,cut j∈bad ∨ p ⁻¹' {cut j}=∅ := by
  let K : Set ℝ := range p ∪ insert 0 bad
  have HK : IsCompact K := (isCompact_range hp).union (hb.insert 0).isCompact
  obtain ⟨L,HL⟩ := HK.bddBelow
  obtain ⟨U,HU⟩ := HK.bddAbove
  have H0 : (0 : ℝ) ∈ K := Or.inr (mem_insert _ _)
  have HLU : L ≤ U := (HL H0).trans (HU H0)
  let A := L-1
  let B := U+1
  have HAB : A < B := by dsimp [A,B]; linarith
  let s : Finset ℝ := insert A (insert B hb.toFinset)
  have HA : A ∈ s := by simp [s]
  have HB : B ∈ s := by simp [s]
  have HS : ∀ t ∈ s, A ≤ t ∧ t ≤ B := by
    intro t ht
    rcases (by simpa [s] using ht : t=A ∨ t=B ∨ t∈bad) with rfl | rfl | ht
    · exact ⟨le_rfl,HAB.le⟩
    · exact ⟨HAB.le,le_rfl⟩
    · have HT : t ∈ K := Or.inr (mem_insert_of_mem _ ht)
      have HTL := HL HT
      have HTU := HU HT
      dsimp [A,B]
      constructor <;> linarith
  have Hcard : 2 ≤ s.card := by
    have Hsub : ({A,B} : Finset ℝ) ⊆ s := by intro t ht; rcases (by simpa using ht : t=A ∨ t=B) with rfl | rfl <;> assumption
    have HH := Finset.card_le_card Hsub
    simpa only [Finset.card_pair (ne_of_lt HAB)] using HH
  have Hfirst : OrderedRealCells.root s ⟨0,by omega⟩ = A := by
    obtain ⟨j,Hj⟩ := OrderedRealCells.exists_root s A HA
    apply le_antisymm
    · rw [← Hj]
      exact (OrderedRealCells.root_strictMono s).monotone (by change 0 ≤ j.val; omega)
    · exact (HS _ (OrderedRealCells.root_mem _ _)).1
  have Hlast : OrderedRealCells.root s ⟨s.card-1,by omega⟩ = B := by
    obtain ⟨j,Hj⟩ := OrderedRealCells.exists_root s B HB
    apply le_antisymm
    · exact (HS _ (OrderedRealCells.root_mem _ _)).2
    · rw [← Hj]
      exact (OrderedRealCells.root_strictMono s).monotone (by have HJ := j.isLt; change j.val ≤ s.card-1; omega)
  let n := s.card-2
  have Hsize : n+2 = s.card := by dsimp [n]; omega
  let cut : Fin (n+2) → ℝ := fun i => OrderedRealCells.root s (Fin.cast Hsize i)
  have HM : StrictMono cut := by
    intro i j hij
    apply OrderedRealCells.root_strictMono s
    exact hij
  have HC0 : cut 0 = A := Hfirst
  have HCN : cut (Fin.last (n+1)) = B := by
    change OrderedRealCells.root s _ = B
    convert Hlast using 1
    apply congrArg
    apply Fin.ext
    simp only [Fin.val_cast,Fin.val_last]
    omega
  refine ⟨n,cut,HM,?_,?_,?_,?_⟩
  · intro t ht
    have HT : t ∈ s := by simp [s,ht]
    obtain ⟨j,Hj⟩ := OrderedRealCells.exists_root s t HT
    exact ⟨Fin.cast Hsize.symm j,by simpa only [cut,Fin.cast_cast,Fin.cast_eq_self] using Hj⟩
  · intro x
    rw [HC0,HCN]
    have HX : p x ∈ K := Or.inl (mem_range_self x)
    have HXL := HL HX
    have HXU := HU HX
    dsimp [A,B]
    constructor <;> linarith
  · intro i t ht hbad
    have HT : t ∈ s := by simp [s,hbad]
    obtain ⟨j,Hj⟩ := OrderedRealCells.exists_root s t HT
    let q : Fin (n+2) := Fin.cast Hsize.symm j
    have HQ : cut q = t := by simpa only [cut,q,Fin.cast_cast,Fin.cast_eq_self] using Hj
    by_cases Hqi : q ≤ i.castSucc
    · have Hle := HM.monotone Hqi
      rw [HQ] at Hle
      exact (not_lt_of_ge Hle) ht.1
    · have Hqi' : i.succ ≤ q := by change i.val+1 ≤ q.val; change ¬ q.val ≤ i.val at Hqi; omega
      have Hle := HM.monotone Hqi'
      rw [HQ] at Hle
      exact (not_lt_of_ge Hle) ht.2
  · intro j
    have HJ : cut j∈s:=OrderedRealCells.root_mem _ _
    rcases (by simpa only [s,Finset.mem_insert,Set.Finite.mem_toFinset] using HJ :
        cut j=A ∨ cut j=B ∨ cut j∈bad) with HJA | HJB | HJbad
    · right
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have HX : p x=cut j:=hx
      rw [HJA] at HX
      have HLX:=HL (Or.inl (mem_range_self x) : p x∈K)
      dsimp only [A] at HX
      linarith
    · right
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have HX : p x=cut j:=hx
      rw [HJB] at HX
      have HUX:=HU (Or.inl (mem_range_self x) : p x∈K)
      dsimp only [B] at HX
      linarith
    · exact Or.inl HJbad

end LeanCanny.Connectivity.FiniteCriticalSweepOrigins
