/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialBranchProduction
public import LeanCanny.Connectivity.FormulaSignSlotRadialAccess
/-! # Actual accessibility of every selected sign-piece boundary point

The branch is constructed from the original source. Only the old projected
coordinates need an endpoint: their squared distance is the radius parameter.
Thus the chosen endpoint and component label are preserved without lifting an
absolute eliminant root or imposing uniqueness on auxiliary witness limits.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotBoundaryAccess
open ETR Set Polynomial LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra
open FormulaSignSlotMarginProjection FormulaSignSlotMarginMaxima FormulaSignSlotComponentMaxima
open FormulaSignSlotRadialAccess
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotMargin.initialDimension FormulaSignSlotSource.dimension
  FormulaSignSlotMargin.initialPolynomial

theorem joined_boundary_piece (c : List Bool) {I : Type*} (C : ClopenPathCover (Positive c) I) (i : I)
    (x : Source c) (hx : x∈closure (ambient c (C.piece i))) (hn : x∉ambient c (C.piece i))
    (y : Fin (FormulaSignSlotSource.dimension c) → ℝ) (hy : y∈projectedPiece c (C.piece i)) :
    JoinedIn (insert (projection c x).val (projectedPiece c (C.piece i))) (projection c x).val y := by
  obtain ⟨b,_HB,t₀,f,HC,HD⟩ := FormulaSignSlotRadialBranchProduction.exists_positive_branch c (C.piece i) (C.clopen i) x hx hn
  let F : ℝ → Source c := fun t => if h : t∈Ioo 0 b then (f ⟨t,h⟩).val else x
  have HE (t : Ioo (0 : ℝ) b) : F t.val=(f t).val := by simp only [F,dite_eq_left t.property]
  have HF : ContinuousOn F (Ioo 0 b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp f.continuous using 1
    funext t
    exact HE t
  have HP (t : ℝ) (ht : t∈Ioo 0 b) : 0 < value c (F t) := by
    rw [HE ⟨t,ht⟩]
    exact (f ⟨t,ht⟩).property
  have HR (t : ℝ) (ht : t∈Ioo 0 b) : SquaredDistanceFibers.value (projection c x).val (projection c (F t)).val=t := by
    rw [HE ⟨t,ht⟩]
    exact HD ⟨t,ht⟩
  have HI : F t₀.val∈ambient c (C.piece i) := by
    rw [HE t₀]
    exact ⟨f t₀,HC t₀,rfl⟩
  exact FormulaSignSlotRadialAccess.joined_center_piece c C i (projection c x).val b F HF HP HR
    t₀.val t₀.property HI y hy
end LeanCanny.Connectivity.FormulaSignSlotBoundaryAccess
