/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.OrderedRealCells
public import LeanCanny.Algebra.ScaledSignQueries
/-! # An ordinal root lies in a window exactly when two root counts permit it

Counts are over distinct real roots, including roots unused by a physical
system. This is a finite counting identity, not a coefficient-sign evaluator.
-/
@[expose] public section
namespace LeanCanny.Geometry.OrderedRealRootWindow
open Set Polynomial LeanCanny.Algebra
open scoped Classical

noncomputable def rank (s : Finset ℝ) (z : ℝ) : ℕ := (s.filter (fun u=>u<z)).card

theorem root_gt_iff (s : Finset ℝ) (i : Fin s.card) (x : ℝ) :
    x<OrderedRealCells.root s i↔(s.filter (fun u=>u≤x)).card ≤ i.val := by
  have HR:=OrderedRealCells.root_rank s i
  constructor
  · intro H
    rw [HR]
    apply Finset.card_le_card
    intro u hu
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,((Finset.mem_filter.mp hu).2).trans_lt H⟩
  · intro H
    by_contra Hnot
    have Hle : OrderedRealCells.root s i≤x:=le_of_not_gt Hnot
    have HS : s.filter (fun u=>u<OrderedRealCells.root s i)⊂s.filter (fun u=>u≤x) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_,?_⟩
      · intro u hu
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,((Finset.mem_filter.mp hu).2).le.trans Hle⟩
      · intro HE
        have HM : OrderedRealCells.root s i∈s.filter (fun u=>u≤x):=
          Finset.mem_filter.mpr ⟨OrderedRealCells.root_mem s i,Hle⟩
        rw [←HE] at HM
        exact (lt_irrefl _) (Finset.mem_filter.mp HM).2
    have HC:=Finset.card_lt_card HS
    omega

theorem exists_rank_window (s : Finset ℝ) (k : ℕ) (lo hi : ℝ) :
    (∃ z∈s,rank s z=k ∧ lo<z ∧ z<hi)↔
      (s.filter (fun u=>u≤lo)).card≤k ∧ k<(s.filter (fun u=>u<hi)).card := by
  constructor
  · rintro ⟨z,hz,HK,HL,HH⟩
    obtain ⟨i,rfl⟩:=OrderedRealCells.exists_root s z hz
    have HR : rank s (OrderedRealCells.root s i)=i.val:=(OrderedRealCells.root_rank s i).symm
    rw [HR] at HK
    subst k
    exact ⟨(root_gt_iff s i lo).mp HL,(OrderedRealCells.root_lt_iff s i hi).mp HH⟩
  · rintro ⟨HL,HH⟩
    have HK : k<s.card:=HH.trans_le (Finset.card_filter_le s _)
    let i : Fin s.card:=⟨k,HK⟩
    exact ⟨OrderedRealCells.root s i,OrderedRealCells.root_mem s i,
      (OrderedRealCells.root_rank s i).symm,(root_gt_iff s i lo).mpr HL,
      (OrderedRealCells.root_lt_iff s i hi).mpr HH⟩

theorem exists_rank_window_gt (s : Finset ℝ) (k : ℕ) (lo hi : ℝ) :
    (∃ z∈s,rank s z=k ∧ lo<z ∧ z<hi)↔
      s.card≤k+(s.filter (fun u=>lo<u)).card ∧ k<(s.filter (fun u=>u<hi)).card := by
  have HP:=Finset.card_filter_add_card_filter_not (s:=s) (fun u=>lo<u)
  have HE : s.filter (fun u=>¬lo<u)=s.filter (fun u=>u≤lo) := by
    ext u
    simp only [Finset.mem_filter,not_lt]
  rw [HE] at HP
  rw [exists_rank_window]
  omega

theorem negative_count (s : Finset ℝ) (x : ℝ) :
    RootSignQueries.signCount s (fun _ : Fin 1=>X-C x) (fun _=>SignType.neg)=
      (s.filter (fun u=>u<x)).card := by
  unfold RootSignQueries.signCount
  congr 1
  ext u
  simp only [Finset.mem_filter,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  have HS : SignType.sign (u-x)=SignType.neg↔u<x := by
    change SignType.sign (u-x)=(-1 : SignType)↔u<x
    rw [sign_eq_neg_one_iff,sub_neg]
  constructor
  · rintro ⟨hu,H⟩
    exact ⟨hu,HS.mp (H 0)⟩
  · rintro ⟨hu,H⟩
    exact ⟨hu,fun _=>HS.mpr H⟩

theorem positive_count (s : Finset ℝ) (x : ℝ) :
    RootSignQueries.signCount s (fun _ : Fin 1=>X-C x) (fun _=>SignType.pos)=
      (s.filter (fun u=>x<u)).card := by
  unfold RootSignQueries.signCount
  congr 1
  ext u
  simp only [Finset.mem_filter,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  have HS : SignType.sign (u-x)=SignType.pos↔x<u := by
    change SignType.sign (u-x)=(1 : SignType)↔x<u
    rw [sign_eq_one_iff,sub_pos]
  constructor
  · rintro ⟨hu,H⟩
    exact ⟨hu,HS.mp (H 0)⟩
  · rintro ⟨hu,H⟩
    exact ⟨hu,fun _=>HS.mpr H⟩

theorem exists_rank_window_signCounts (s : Finset ℝ) (k : ℕ) (lo hi : ℝ) :
    (∃ z∈s,rank s z=k ∧ lo<z ∧ z<hi)↔
      s.card≤k+RootSignQueries.signCount s (fun _ : Fin 1=>X-C lo) (fun _=>SignType.pos) ∧
      k<RootSignQueries.signCount s (fun _ : Fin 1=>X-C hi) (fun _=>SignType.neg) := by
  rw [positive_count,negative_count,exists_rank_window_gt]

end LeanCanny.Geometry.OrderedRealRootWindow
