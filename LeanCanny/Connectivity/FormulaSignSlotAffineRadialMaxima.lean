/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialFeatureSource
/-! # Component-preserving local maxima on literal affine radial slices

The component label, old tuple, literal margin objective, and single initial
quadratic feature are retained together. No regularity or finite critical-arc
coverage is inferred from the compactness argument.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotAffineRadialMaxima
open Set ETR LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotMarginProjection FormulaSignSlotMarginMaxima FormulaSignSlotComponentMaxima
open FormulaSignSlotRadialFeature
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def affineSphere (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (r : ℝ) : Set (Lifted c) := {y | SquaredDistanceLinearization.affine center
      (y.val (Fin.last (FormulaSignSlotMargin.initialDimension c))) (oldTuple c y)=r}

theorem sphere_eq (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ) (r : ℝ) :
    affineSphere c center r=liftedSphere c center r := by
  ext y
  exact (sphere_affine c center r y).symm

theorem cover_boundary_maxima (c : List Bool) {I : Type*}
    (C : ClopenPathCover (Positive c) I) (i : I)
    (x : Source c) (hx : x∈closure (ambient c (C.piece i)))
    (hn : x∉ambient c (C.piece i)) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ ∃ y : Lifted c,
      homeomorph c y∈ambient c (C.piece i) ∧
      y∈affineSphere c (projection c x).val r ∧
      IsLocalMaxOn (fun z : Lifted c => z.val (Fin.castAdd 1 (objectiveIndex c)))
        (affineSphere c (projection c x).val r) y ∧
      0 < y.val (Fin.castAdd 1 (objectiveIndex c)) := by
  obtain ⟨r,hr,hεr,z,hz,hzS,HM,HP⟩ := FormulaSignSlotLocalMaxima.cover_boundary_maxima c C i x hx hn ε hε
  let y := (homeomorph c).symm z
  have HE : homeomorph c y=z := (homeomorph c).apply_symm_apply z
  have HY : y∈liftedSphere c (projection c x).val r := by
    change homeomorph c y∈sourceSphere c (projection c x).val r
    rwa [HE]
  have HM' : IsLocalMaxOn (value c) (sourceSphere c (projection c x).val r) (homeomorph c y) := by rwa [HE]
  refine ⟨r,hr,hεr,y,?_,?_,?_,?_⟩
  · rwa [HE]
  · rwa [sphere_eq]
  · rw [sphere_eq]
    exact FormulaSignSlotRadialFeature.local_maximum c _ r y HY HM'
  · rw [margin_coordinate,HE]
    exact HP

end LeanCanny.Connectivity.FormulaSignSlotAffineRadialMaxima
