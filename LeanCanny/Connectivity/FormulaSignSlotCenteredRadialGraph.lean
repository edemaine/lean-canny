/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CenteredRadialGraph
public import LeanCanny.Connectivity.FormulaSignSlotLocalMaxima
public import LeanCanny.Connectivity.FormulaSignSlotRadialFeature
/-! # The actual margin source with a universal centered radial coordinate

Centers are appended spatial coordinates. Freezing those coordinates and the
radius coordinate uses fixed integer coordinate normals, even for centers
represented by the selected parent algebra homomorphism.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotCenteredRadialGraph
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotMarginProjection FormulaSignSlotMarginMaxima FormulaSignSlotComponentMaxima
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev N (c : List Bool) := FormulaSignSlotMargin.initialDimension c
noncomputable abbrev d (c : List Bool) := FormulaSignSlotSource.dimension c
noncomputable abbrev p (c : List Bool) := FormulaSignSlotMargin.initialPolynomial c

theorem scope (c : List Bool) : (p c).arity≤N c := FormulaSignSlotRadialFeature.source_scope c

theorem d_le (c : List Bool) : d c≤N c := FormulaSignSlotRadialFeature.old_dimension_le c

noncomputable abbrev Graph (c : List Bool) := CenteredRadialGraph.Graph (N c) (d c) (p c)
noncomputable def forget (c : List Bool) : Graph c → Source c := CenteredRadialGraph.oldPoint _ _ _ (scope c)
noncomputable def center (c : List Bool) : Graph c → (Fin (d c) → ℝ) := CenteredRadialGraph.center _ _ _ (scope c)
noncomputable def lift (c : List Bool) (a : Fin (d c) → ℝ) (x : Source c) : Graph c :=
  CenteredRadialGraph.lift _ _ _ (scope c) a x

theorem forget_lift (c : List Bool) (a : Fin (d c) → ℝ) (x : Source c) : forget c (lift c a x)=x :=
  CenteredRadialGraph.oldPoint_section _ _ _ (scope c) a x

theorem center_lift (c : List Bool) (a : Fin (d c) → ℝ) (x : Source c) : center c (lift c a x)=a :=
  CenteredRadialGraph.center_section _ _ _ (scope c) a x

noncomputable def centerIndex (c : List Bool) (i : Fin (d c)) : Fin (N c+d c+1) :=
  Fin.castAdd 1 (Fin.natAdd (N c) i)
noncomputable def radiusIndex (c : List Bool) : Fin (N c+d c+1) := Fin.last (N c+d c)
noncomputable def marginIndex (c : List Bool) : Fin (N c+d c+1) :=
  Fin.castAdd 1 (Fin.castAdd (d c) (objectiveIndex c))

theorem center_coordinate (c : List Bool) (y : Graph c) (i : Fin (d c)) :
    center c y i=y.val (centerIndex c i) := rfl

theorem radius_coordinate (c : List Bool) (y : Graph c) : y.val (radiusIndex c)=
    SquaredDistanceFibers.value (center c y) (projection c (forget c y)).val := by
  have H := CenteredRadialGraph.radius_coordinate (N c) (d c) (p c) (scope c) (d_le c) y
  apply H.trans
  apply congrArg (SquaredDistanceFibers.value (center c y))
  funext i
  rw [projection_coordinate]
  rfl

theorem margin_coordinate (c : List Bool) (y : Graph c) : y.val (marginIndex c)=value c (forget c y) := rfl

noncomputable def slice (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) : Set (Graph c) :=
  {y | (∀ i, y.val (centerIndex c i)=a i) ∧ y.val (radiusIndex c)=r}

theorem forget_slice (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) :
    MapsTo (forget c) (slice c a r) (sourceSphere c a r) := by
  intro y hy
  have HC : center c y=a := funext hy.1
  change SquaredDistanceFibers.value a (projection c (forget c y)).val=r
  rw [← HC,← radius_coordinate]
  exact hy.2

theorem lift_slice (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (x : Source c)
    (hx : x∈sourceSphere c a r) : lift c a x∈slice c a r := by
  constructor
  · intro i
    rw [← center_coordinate,center_lift]
  · rw [radius_coordinate,center_lift,forget_lift]
    exact hx

theorem local_maximum (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (x : Source c)
    (hx : x∈sourceSphere c a r) (HM : IsLocalMaxOn (value c) (sourceSphere c a r) x) :
    IsLocalMaxOn (fun y : Graph c => y.val (marginIndex c)) (slice c a r) (lift c a x) := by
  have HH : IsLocalMaxOn (value c) (sourceSphere c a r) (forget c (lift c a x)) := by rwa [forget_lift]
  exact HH.comp_continuousOn (forget_slice c a r)
    (CenteredRadialGraph.oldPoint_continuous _ _ _ (scope c)).continuousOn (lift_slice c a r x hx)

theorem slice_image (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) :
    slice c a r=lift c a '' sourceSphere c a r := by
  ext y
  constructor
  · intro hy
    refine ⟨forget c y,forget_slice c a r hy,?_⟩
    have HC : center c y=a := funext hy.1
    rw [← HC]
    exact CenteredRadialGraph.lift_forget _ _ _ (scope c) y
  · rintro ⟨x,hx,rfl⟩
    exact lift_slice c a r x hx

theorem compact_slice (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (hr : 0≤r) :
    IsCompact (slice c a r) := by
  rw [slice_image]
  exact (compact_sourceSphere c a r hr).image (CenteredRadialGraph.lift_continuous _ _ _ (scope c) a)

theorem cover_boundary_maxima (c : List Bool) {I : Type*}
    (C : ClopenPathCover (Positive c) I) (i : I) (x : Source c)
    (hx : x∈closure (ambient c (C.piece i))) (hn : x∉ambient c (C.piece i))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ ∃ y : Graph c,
      forget c y∈ambient c (C.piece i) ∧ y∈slice c (projection c x).val r ∧
      IsLocalMaxOn (fun z : Graph c => z.val (marginIndex c)) (slice c (projection c x).val r) y ∧
      0 < y.val (marginIndex c) := by
  obtain ⟨r,hr,hεr,z,hz,hzS,HM,HP⟩ := FormulaSignSlotLocalMaxima.cover_boundary_maxima c C i x hx hn ε hε
  refine ⟨r,hr,hεr,lift c (projection c x).val z,?_,lift_slice c _ r z hzS,local_maximum c _ r z hzS HM,?_⟩
  · rwa [forget_lift]
  · rwa [margin_coordinate,forget_lift]

end LeanCanny.Connectivity.FormulaSignSlotCenteredRadialGraph
