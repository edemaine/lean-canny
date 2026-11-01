/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineShiftedSliceProjection
/-! # Typed actual coarse-slice sections under a fixed scalar translation -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineTranslatedSections
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineShiftedSlice (projection)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {J : Type}

theorem exists_lift (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (hh : h ∈ FlatAffineFullSourceTower.free F u (F.depth u)) (α A B : ℝ) (t₀ : Ioo A B)
    (curve : J → ℝ → Fin (arity F u) → ℝ) (HC : ∀ j, ContinuousOn (curve j) (Icc A B))
    (HR : ∀ j t, t ∈ Icc A B → curve j t ∈ FlatAffineShiftedSlice.slice F u x h (α+t))
    (HS : ∀ t : Ioo A B, ∀ y ∈ FlatAffineShiftedSlice.slice F u x h (α+t.val),
      ∃ j, JoinedIn (FlatAffineShiftedSlice.slice F u x h (α+t.val)) y (curve j t.val)) :
    ∃ arc : J → ℝ → FlatAffineShiftedSlice.coarseSlice F u x h,
      (∀ j, ContinuousOn (arc j) (Icc (α+A) (α+B))) ∧
      (∀ j t, t ∈ Icc (α+A) (α+B) → projection F u x h (arc j t) = t) ∧
      (∀ j t, t ∈ Icc (α+A) (α+B) → (arc j t).val = curve j (t-α)) ∧
      ∀ t : Ioo (α+A) (α+B), ∀ y : FlatAffineShiftedSlice.coarseSlice F u x h,
        projection F u x h y = t.val → ∃ j, JoinedIn ((projection F u x h) ⁻¹' {t.val}) y (arc j t.val) := by
  have Hdelta (t : ℝ) (ht : t ∈ Icc (α+A) (α+B)) : t-α ∈ Icc A B := by constructor <;> linarith [ht.1,ht.2]
  have Hroot (j : J) (t : ℝ) (ht : t ∈ Icc (α+A) (α+B)) : curve j (t-α) ∈ FlatAffineShiftedSlice.slice F u x h t := by
    have H := HR j (t-α) (Hdelta t ht)
    simpa only [show α+(t-α)=t by ring] using H
  let anchor (j : J) : FlatAffineShiftedSlice.coarseSlice F u x h :=
    ⟨curve j t₀.val, ((FlatAffineShiftedSlice.slice_iff_fiber F u x h hh (α+t₀.val) _).mp
      (HR j t₀.val (Ioo_subset_Icc_self t₀.property))).1⟩
  let arc (j : J) (t : ℝ) : FlatAffineShiftedSlice.coarseSlice F u x h :=
    if ht : t ∈ Icc (α+A) (α+B) then ⟨curve j (t-α),
      ((FlatAffineShiftedSlice.slice_iff_fiber F u x h hh t _).mp (Hroot j t ht)).1⟩ else anchor j
  have HA (j : J) : ContinuousOn (arc j) (Icc (α+A) (α+B)) := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    have HD : ContinuousOn (fun t : ℝ => curve j (t-α)) (Icc (α+A) (α+B)) :=
      (HC j).comp (continuous_id.sub continuous_const).continuousOn (fun t ht => Hdelta t ht)
    apply HD.congr
    intro t ht
    simp only [arc, dite_eq_left ht, Function.comp_apply]
  have HL (j : J) (t : ℝ) (ht : t ∈ Icc (α+A) (α+B)) : projection F u x h (arc j t) = t := by
    simp only [arc, dite_eq_left ht]
    exact ((FlatAffineShiftedSlice.slice_iff_fiber F u x h hh t _).mp (Hroot j t ht)).2
  have HV (j : J) (t : ℝ) (ht : t ∈ Icc (α+A) (α+B)) : (arc j t).val = curve j (t-α) := by simp only [arc,dite_eq_left ht]
  refine ⟨arc,HA,HL,HV,?_⟩
  intro t y hy
  let δ : Ioo A B := ⟨t.val-α,by constructor <;> linarith [t.property.1,t.property.2]⟩
  have HE : α+δ.val=t.val := by dsimp only [δ]; ring
  have HY := (FlatAffineShiftedSlice.slice_iff_fiber F u x h hh t.val y.val).mpr ⟨y.property,hy⟩
  obtain ⟨j,HJ⟩ := HS δ y.val (by simpa only [HE] using HY)
  refine ⟨j,(FlatAffineShiftedSlice.joined_fiber_iff F u x h hh t.val y (arc j t.val) hy
    (HL j t.val (Ioo_subset_Icc_self t.property))).mpr ?_⟩
  rw [HV j t.val (Ioo_subset_Icc_self t.property)]
  simpa only [HE] using HJ

end LeanCanny.Connectivity.FlatAffineTranslatedSections
