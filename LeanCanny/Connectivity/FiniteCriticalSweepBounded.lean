/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.OrderedRealCells
public import LeanCanny.Algebra.PowerIntegerPolynomial
public import Mathlib.Data.Set.Card
/-! # Sweeps with prescribed outer cuts

The finite bad values are sorted between supplied strict outer bounds.
The power specialization retains exact degree-one integer leaf origins.
No effective bound on the image or bad roots is inferred here.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FiniteCriticalSweepBounded
open Set LeanCanny.Geometry
open scoped Classical

theorem exists_cuts {X : Type*} (p : X → ℝ) (bad : Set ℝ) (hb : bad.Finite)
    (A B : ℝ) (hAB : A<B) (hbad : ∀ t∈bad,A<t ∧ t<B) (himage : ∀ x,A<p x ∧ p x<B) :
    ∃ n : ℕ, n≤bad.ncard ∧ ∃ cut : Fin (n+2) → ℝ, StrictMono cut ∧ cut 0=A ∧ cut (Fin.last (n+1))=B ∧
      (∀ t ∈ bad, ∃ j, cut j = t) ∧
      (∀ x, p x ∈ Icc (cut 0) (cut (Fin.last (n+1)))) ∧
      (∀ i : Fin (n+1), ∀ t ∈ Ioo (cut i.castSucc) (cut i.succ), t ∉ bad) ∧
      ∀ j,cut j∈bad ∨ p ⁻¹' {cut j}=∅ := by
  let s : Finset ℝ := insert A (insert B hb.toFinset)
  have HA : A ∈ s := by simp [s]
  have HB : B ∈ s := by simp [s]
  have HS : ∀ t ∈ s, A ≤ t ∧ t ≤ B := by
    intro t ht
    rcases (by simpa [s] using ht : t=A ∨ t=B ∨ t∈bad) with rfl | rfl | ht
    · exact ⟨le_rfl,hAB.le⟩
    · exact ⟨hAB.le,le_rfl⟩
    · exact ⟨(hbad t ht).1.le,(hbad t ht).2.le⟩
  have Hcard : 2 ≤ s.card := by
    have Hsub : ({A,B} : Finset ℝ) ⊆ s := by intro t ht; rcases (by simpa using ht : t=A ∨ t=B) with rfl | rfl <;> assumption
    have HH := Finset.card_le_card Hsub
    simpa only [Finset.card_pair (ne_of_lt hAB)] using HH
  have Hfirst : OrderedRealCells.root s ⟨0,by omega⟩ = A := by
    obtain ⟨j,Hj⟩ := OrderedRealCells.exists_root s A HA
    apply le_antisymm
    · exact ((OrderedRealCells.root_strictMono s).monotone (by change 0 ≤ j.val; omega)).trans_eq Hj
    · exact (HS _ (OrderedRealCells.root_mem _ _)).1
  have Hlast : OrderedRealCells.root s ⟨s.card-1,by omega⟩ = B := by
    obtain ⟨j,Hj⟩ := OrderedRealCells.exists_root s B HB
    apply le_antisymm
    · exact (HS _ (OrderedRealCells.root_mem _ _)).2
    · exact Hj.symm.trans_le ((OrderedRealCells.root_strictMono s).monotone (by have HJ := j.isLt; change j.val ≤ s.card-1; omega))
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
  have HN : n≤bad.ncard := by
    have Hcardle : s.card≤hb.toFinset.card+2 := by
      exact (Finset.card_insert_le _ _).trans ((Nat.add_le_add_right (Finset.card_insert_le _ _) 1).trans (by omega))
    have Hbad : bad.ncard=hb.toFinset.card:=Set.ncard_eq_toFinset_card bad hb
    dsimp only [n]
    omega
  refine ⟨n,HN,cut,HM,HC0,HCN,?_,?_,?_,?_⟩
  · intro t ht
    have HT : t ∈ s := by simp [s,ht]
    obtain ⟨j,Hj⟩ := OrderedRealCells.exists_root s t HT
    exact ⟨Fin.cast Hsize.symm j,by simpa only [cut,Fin.cast_cast,Fin.cast_eq_self] using Hj⟩
  · intro x
    rw [HC0,HCN]
    exact ⟨(himage x).1.le,(himage x).2.le⟩
  · intro i t ht htbad
    have HT : t ∈ s := by simp [s,htbad]
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
      exact (ne_of_gt (himage x).1) HX
    · right
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have HX : p x=cut j:=hx
      rw [HJB] at HX
      exact (ne_of_lt (himage x).2) HX
    · exact Or.inl HJbad

theorem exists_clipped_cuts {X : Type*} (p : X→ℝ) (bad : Set ℝ) (hb : bad.Finite)
    (A B : ℝ) (hAB : A<B) (himage : ∀ x,A<p x ∧ p x<B) :
    ∃ n : ℕ,n≤bad.ncard ∧ ∃ cut : Fin (n+2)→ℝ,StrictMono cut ∧
      cut 0=A ∧ cut (Fin.last (n+1))=B ∧
      (∀ t∈bad∩Ioo A B,∃ j,cut j=t) ∧
      (∀ x,p x∈Icc (cut 0) (cut (Fin.last (n+1)))) ∧
      (∀ i : Fin (n+1),∀ t∈Ioo (cut i.castSucc) (cut i.succ),t∉bad) ∧
      ∀ j,cut j∈bad ∨ p ⁻¹' {cut j}=∅ := by
  obtain ⟨n,Hn,cut,HM,H0,Hlast,Hbad,Hbound,Havoid,Horig⟩:=
    exists_cuts p (bad∩Ioo A B) (hb.subset Set.inter_subset_left) A B hAB
      (fun _ ht=>ht.2) himage
  refine ⟨n,Hn.trans (Set.ncard_le_ncard Set.inter_subset_left hb),cut,HM,H0,Hlast,Hbad,Hbound,?_,?_⟩
  · intro i t ht htbad
    have HL : A≤cut i.castSucc := by
      rw [←H0]
      exact HM.monotone (Fin.zero_le _)
    have HR : cut i.succ≤B := by
      rw [←Hlast]
      exact HM.monotone (Fin.le_last _)
    exact Havoid i t ht ⟨htbad,lt_of_le_of_lt HL ht.1,lt_of_lt_of_le ht.2 HR⟩
  · intro j
    exact (Horig j).imp (fun ht=>ht.1) id

theorem exists_power_cuts {X : Type*} (p : X→ℝ) (bad : Set ℝ) (hb : bad.Finite) (E : ℕ)
    (hbad : ∀ t∈bad,|t|<(2 : ℝ)^E) (himage : ∀ x,|p x|<(2 : ℝ)^E) :
    ∃ n : ℕ,n≤bad.ncard ∧ ∃ cut : Fin (n+2)→ℝ,StrictMono cut ∧
      cut 0=-(2 : ℝ)^E ∧ cut (Fin.last (n+1))=(2 : ℝ)^E ∧
      (∀ t∈bad,∃ j,cut j=t) ∧
      (∀ x,p x∈Icc (cut 0) (cut (Fin.last (n+1)))) ∧
      (∀ i : Fin (n+1),∀ t∈Ioo (cut i.castSucc) (cut i.succ),t∉bad) ∧
      ∀ j,cut j∈bad ∨ p ⁻¹' {cut j}=∅ :=
  exists_cuts p bad hb _ _ (by have HP : 0<(2 : ℝ)^E:=pow_pos (by norm_num) E; linarith) (fun t ht=>abs_lt.mp (hbad t ht)) (fun x=>abs_lt.mp (himage x))

theorem exists_clipped_power_cuts {X : Type*} (p : X→ℝ) (bad : Set ℝ) (hb : bad.Finite) (E : ℕ)
    (himage : ∀ x,|p x|<(2 : ℝ)^E) :
    ∃ n : ℕ,n≤bad.ncard ∧ ∃ cut : Fin (n+2)→ℝ,StrictMono cut ∧
      cut 0=-(2 : ℝ)^E ∧ cut (Fin.last (n+1))=(2 : ℝ)^E ∧
      (∀ t∈bad∩Ioo (-(2 : ℝ)^E) ((2 : ℝ)^E),∃ j,cut j=t) ∧
      (∀ x,p x∈Icc (cut 0) (cut (Fin.last (n+1)))) ∧
      (∀ i : Fin (n+1),∀ t∈Ioo (cut i.castSucc) (cut i.succ),t∉bad) ∧
      ∀ j,cut j∈bad ∨ p ⁻¹' {cut j}=∅ :=
  exists_clipped_cuts p bad hb _ _ (by have HP : 0<(2 : ℝ)^E:=pow_pos (by norm_num) E; linarith)
    (fun x=>abs_lt.mp (himage x))

theorem left_power_origin (E : ℕ) :
    (LeanCanny.Algebra.PowerIntegerPolynomial.polynomial True E).eval₂ (Int.castRingHom ℝ) (-(2 : ℝ)^E)=0 := by
  rw [LeanCanny.Algebra.PowerIntegerPolynomial.root_iff]
  simp only [LeanCanny.Algebra.PowerIntegerPolynomial.value,ite_true,Int.cast_neg,Int.cast_pow,Int.cast_ofNat]

theorem right_power_origin (E : ℕ) :
    (LeanCanny.Algebra.PowerIntegerPolynomial.polynomial False E).eval₂ (Int.castRingHom ℝ) ((2 : ℝ)^E)=0 := by
  rw [LeanCanny.Algebra.PowerIntegerPolynomial.root_iff]
  simp only [LeanCanny.Algebra.PowerIntegerPolynomial.value,ite_false,Int.cast_pow,Int.cast_ofNat]

end LeanCanny.Connectivity.FiniteCriticalSweepBounded
