/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.OrderedRealCells
public import LeanCanny.Connectivity.FiniteSlabCover
/-! # A finite sweep uses only its actual cuts

Distinct extrema give proper consecutive slabs. Equal extrema give one
fiber, handled by degenerate descent. No artificial endpoint is inserted.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FiniteCriticalSweepInternal
open Set LeanCanny.Geometry
open scoped Classical

theorem adjacent_cover {n : ℕ} (cut : Fin (n+2)→ℝ) {x : ℝ}
    (hx : x∈Icc (cut 0) (cut (Fin.last (n+1)))) :
    ∃i : Fin (n+1),x∈Icc (cut i.castSucc) (cut i.succ) :=by
  let C : ℕ→ℝ:=fun i=>if hi : i<n+2 then cut ⟨i,hi⟩ else 0
  have H0 : C 0=cut 0:=by simp only [C,dite_eq_left (show 0<n+2 by omega)];rfl
  have HN : C (n+1)=cut (Fin.last (n+1)):=by
    simp only [C,dite_eq_left (show n+1<n+2 by omega)]
    rfl
  obtain ⟨i,HI⟩:=FiniteSlabCover.exists_adjacent_interval C n (by rwa [H0,HN])
  have HA : C i.val=cut i.castSucc:=by
    rw [show C i.val=cut ⟨i.val,by have :=i.isLt;omega⟩ from dite_eq_left (by have :=i.isLt;omega)]
    apply congrArg cut
    apply Fin.ext
    rfl
  have HB : C (i.val+1)=cut i.succ:=by
    rw [show C (i.val+1)=cut ⟨i.val+1,by have :=i.isLt;omega⟩ from dite_eq_left (by have :=i.isLt;omega)]
    apply congrArg cut
    apply Fin.ext
    rfl
  exact ⟨i,by rwa [HA,HB] at HI⟩

theorem singleton_of_equal_extrema (s : Finset ℝ) (a : ℝ)
    (ha : IsLeast (s : Set ℝ) a) (hb : IsGreatest (s : Set ℝ) a) : s={a} :=by
  ext t
  simp only [Finset.mem_singleton]
  constructor
  · intro ht
    exact le_antisymm (hb.2 ht) (ha.2 ht)
  · rintro rfl
    exact ha.1

theorem extrema_cases (s : Finset ℝ) (a b : ℝ)
    (ha : IsLeast (s : Set ℝ) a) (hb : IsGreatest (s : Set ℝ) b) :
    (a=b ∧ s={a}) ∨a<b :=by
  by_cases hab : a<b
  · exact Or.inr hab
  · have HE : a=b:=le_antisymm (ha.2 hb.1) (le_of_not_gt hab)
    exact Or.inl ⟨HE,singleton_of_equal_extrema s a ha (HE.symm ▸hb)⟩

theorem exists_cuts (s : Finset ℝ) (a b : ℝ)
    (ha : IsLeast (s : Set ℝ) a) (hb : IsGreatest (s : Set ℝ) b) (hab : a<b) :
    ∃n : ℕ,∃cut : Fin (n+2)→ℝ,StrictMono cut ∧ cut 0=a ∧ cut (Fin.last (n+1))=b ∧
      (∀j,cut j∈s) ∧ (∀t∈s,∃j,cut j=t) ∧
      (∀i : Fin (n+1),∀t∈Ioo (cut i.castSucc) (cut i.succ),t∉s) ∧
      ∀t∈Icc a b,∃i : Fin (n+1),t∈Icc (cut i.castSucc) (cut i.succ) :=by
  have Hcard : 2≤s.card:=by
    have HS : ({a,b} : Finset ℝ)⊆s:=by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl|ht
      · exact ha.1
      · exact Finset.mem_singleton.mp ht ▸ hb.1
    simpa only [Finset.card_pair hab.ne] using Finset.card_le_card HS
  have Hfirst : OrderedRealCells.root s ⟨0,by omega⟩=a :=by
    obtain ⟨j,Hj⟩:=OrderedRealCells.exists_root s a ha.1
    apply le_antisymm
    · rw [←Hj]
      exact (OrderedRealCells.root_strictMono s).monotone (by change 0≤j.val;omega)
    · exact ha.2 (OrderedRealCells.root_mem _ _)
  have Hlast : OrderedRealCells.root s ⟨s.card-1,by omega⟩=b :=by
    obtain ⟨j,Hj⟩:=OrderedRealCells.exists_root s b hb.1
    apply le_antisymm
    · exact hb.2 (OrderedRealCells.root_mem _ _)
    · rw [←Hj]
      exact (OrderedRealCells.root_strictMono s).monotone (by have :=j.isLt;change j.val≤s.card-1;omega)
  let n:=s.card-2
  have Hsize : n+2=s.card:=by dsimp [n];omega
  let cut : Fin (n+2)→ℝ:=fun i=>OrderedRealCells.root s (Fin.cast Hsize i)
  have HM : StrictMono cut:=fun _ _ hij=>OrderedRealCells.root_strictMono s hij
  have H0 : cut 0=a:=Hfirst
  have HN : cut (Fin.last (n+1))=b:=by
    change OrderedRealCells.root s _=b
    convert Hlast using 1
    apply congrArg
    apply Fin.ext
    simp only [Fin.val_cast,Fin.val_last]
    omega
  refine ⟨n,cut,HM,H0,HN,fun j=>OrderedRealCells.root_mem s _,?_,?_,?_⟩
  · intro t ht
    obtain ⟨j,Hj⟩:=OrderedRealCells.exists_root s t ht
    exact ⟨Fin.cast Hsize.symm j,by simpa only [cut,Fin.cast_cast,Fin.cast_eq_self] using Hj⟩
  · intro i t ht hmem
    obtain ⟨j,Hj⟩:=OrderedRealCells.exists_root s t hmem
    let q : Fin (n+2):=Fin.cast Hsize.symm j
    have HQ : cut q=t:=by simpa only [cut,q,Fin.cast_cast,Fin.cast_eq_self] using Hj
    by_cases Hqi : q≤i.castSucc
    · have Hle:=HM.monotone Hqi
      rw [HQ] at Hle
      exact (not_lt_of_ge Hle) ht.1
    · have Hqi' : i.succ≤q:=by change i.val+1≤q.val;change ¬q.val≤i.val at Hqi;omega
      have Hle:=HM.monotone Hqi'
      rw [HQ] at Hle
      exact (not_lt_of_ge Hle) ht.2
  · intro t ht
    apply adjacent_cover cut
    rwa [H0,HN]

end LeanCanny.Connectivity.FiniteCriticalSweepInternal
