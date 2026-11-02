/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrame

/-! # An endpoint level becomes the next frame's singled frozen coordinate

The retained scalar is the actual affine level c*y_r-oldHeight. Its new
reference is added to the shifted old height. Coarsening the new frame
recovers the old slice, and its full slice is exactly the selected fiber.
No spatial degree or source polynomial is changed.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n : ℕ}

def level (F : Frame n) (r : Fin (n+1)) : Frame n where
  frozen := insert r F.frozen
  scales := F.scales
  scales_ne_zero := F.scales_ne_zero
  heights i := if i=r then .add (later (F.heights i)) (.reference 0) else later (F.heights i)

noncomputable def projection {m : ℕ} (F : Frame n) (values : Fin m→ℝ) (r : Fin (n+1)) (y : Fin (n+1)→ℝ) : ℝ :=
  (F.scales r:ℝ)*y r-(F.heights r).evaluate values

theorem level_rank (F : Frame n) (r : Fin (n+1)) (hr : r∉F.frozen) :
    n+1-(level F r).frozen.card+1=n+1-F.frozen.card := advance_rank F r hr

theorem level_nodes (F : Frame n) (r i : Fin (n+1)) :
    ((level F r).heights i).nodes≤(F.heights i).nodes+2 := by
  by_cases hi : i=r
  · simp only [level,ite_eq_left hi,AffineExpr.nodes,nodes_later]
    omega
  · simp only [level,ite_eq_right hi,nodes_later]
    omega

theorem level_coefficients (F : Frame n) (r i : Fin (n+1)) (C : ℕ) :
    ((level F r).heights i).CoefficientsBound C↔(F.heights i).CoefficientsBound C := by
  by_cases hi : i=r
  · simp only [level,ite_eq_left hi,AffineExpr.CoefficientsBound,coefficients_later,and_true]
  · simp only [level,ite_eq_right hi,coefficients_later]

theorem evaluate_level_height {m : ℕ} (F : Frame n) (r : Fin (n+1)) (values : Fin m→ℝ) (a : ℝ) :
    ((level F r).heights r).evaluate (Fin.cons a values)=(F.heights r).evaluate values+a := by
  simp only [level,ite_true]
  change (later (F.heights r)).evaluate (Fin.cons a values)+
    (AffineExpr.reference 0).evaluate (Fin.cons a values)=_
  rw [evaluate_later,evaluate_reference_zero]

theorem slice_level {m : ℕ} (P : SpatialSource n) (F : Frame n) (r : Fin (n+1)) (hr : r∉F.frozen)
    (values : Fin m→ℝ) (a : ℝ) :
    slice P (level F r) (Fin.cons a values)=slice P F values∩{y | projection F values r y=a} := by
  ext y
  constructor
  · intro h
    have Hnew:=h.2 r (Finset.mem_insert_self r F.frozen)
    have Hlevel : (F.scales r:ℝ)*y r=(F.heights r).evaluate values+a := by
      rw [evaluate_level_height] at Hnew
      exact Hnew
    have Hcoord : projection F values r y=a := by unfold projection; linarith
    refine ⟨⟨h.1,fun i hi=>?_⟩,Hcoord⟩
    have Hne : i≠r := by intro HE; exact hr (HE ▸ hi)
    have Hold:=h.2 i (Finset.mem_insert_of_mem hi)
    simpa only [level,ite_eq_right Hne,evaluate_later] using Hold
  · rintro ⟨h,Hcoord⟩
    refine ⟨h.1,fun i hi=>?_⟩
    rcases Finset.mem_insert.mp hi with rfl|hi
    · have Hlevel : (F.scales i:ℝ)*y i=(F.heights i).evaluate values+a := by
        change projection F values i y=a at Hcoord
        unfold projection at Hcoord
        linarith
      change (F.scales i:ℝ)*y i=((level F i).heights i).evaluate (Fin.cons a values)
      rw [evaluate_level_height]
      exact Hlevel
    · have Hne : i≠r := by intro HE; exact hr (HE ▸ hi)
      simpa only [level,ite_eq_right Hne,evaluate_later] using h.2 i hi

theorem slice_coarse_level {m : ℕ} (P : SpatialSource n) (F : Frame n) (r : Fin (n+1)) (hr : r∉F.frozen)
    (values : Fin m→ℝ) (a : ℝ) :
    slice P (coarse (level F r) r) (Fin.cons a values)=slice P F values := by
  have HF : (coarse (level F r) r).frozen=F.frozen := by simp only [coarse,level,Finset.erase_insert hr]
  ext y
  constructor
  · intro h
    refine ⟨h.1,fun i hi=>?_⟩
    have Hne : i≠r := by intro HE; exact hr (HE ▸ hi)
    have Hold:=h.2 i (HF.symm ▸ hi)
    simpa only [coarse,level,ite_eq_right Hne,evaluate_later] using Hold
  · intro h
    refine ⟨h.1,fun i hi=>?_⟩
    have Hmem : i∈F.frozen := HF ▸ hi
    have Hne : i≠r := by intro HE; exact hr (HE ▸ Hmem)
    simpa only [coarse,level,ite_eq_right Hne,evaluate_later] using h.2 i Hmem

end LeanCanny.Geometry.IntegralMixedFrozenFrame
