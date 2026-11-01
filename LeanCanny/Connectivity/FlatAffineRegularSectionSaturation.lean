/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineRegularSliceCharts
public import LeanCanny.Connectivity.FiberSectionLimit
public import LeanCanny.Connectivity.ComponentSlabCover
/-! # Actual regular slices saturated by any proved finite physical sections

The projection, local charts, saturated paths and connected endpoint limits
are derived. The sections need only the literal fiber-path sampling property.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineRegularSectionSaturation
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineShiftedSlice (projection)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def sectionMap {X J : Type} [TopologicalSpace X] (p : X → ℝ) (A B : ℝ)
    (arc : J → ℝ → X) (HA : ∀ j, ContinuousOn (arc j) (Icc A B))
    (HL : ∀ j t, t ∈ Icc A B → p (arc j t) = t) (j : J) : C(Ioo A B,p ⁻¹' Ioo A B) where
  toFun t := ⟨arc j t.val, by
    change p (arc j t.val) ∈ Ioo A B
    rw [HL j t.val (Ioo_subset_Icc_self t.property)]
    exact t.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_domRestrict.mp ((HA j).mono Ioo_subset_Icc_self)

theorem exists_interior_data {J : Type} [Finite J] (F : Inputs) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots F u) (h : Fin (arity F u))
    (hh : h ∈ FlatAffineFullSourceTower.free F u (F.depth u)) (A B : ℝ) (t₀ : Ioo A B)
    (HR : FlatAffineSlabRegularData.RegularOn F u x h A B)
    (arc : J → ℝ → FlatAffineShiftedSlice.coarseSlice F u x h)
    (HA : ∀ j, ContinuousOn (arc j) (Icc A B))
    (HL : ∀ j t, t ∈ Icc A B → projection F u x h (arc j t) = t)
    (HS : ∀ t : Ioo A B, ∀ y : FlatAffineShiftedSlice.coarseSlice F u x h,
      projection F u x h y = t.val → ∃ j, JoinedIn ((projection F u x h) ⁻¹' {t.val}) y (arc j t.val)) :
    ∃ D : ComponentSlabCover.InteriorData (projection F u x h) A B J,
      (∀ j, IsClopen (D.piece j)) ∧
      (∀ j t, D.arc j t = arc j t) ∧
      ∀ i j, ClosedPathCover.Overlap D.piece i j ↔
        JoinedIn (FlatAffineShiftedSlice.slice F u x h t₀.val) (arc i t₀.val).val (arc j t₀.val).val := by
  let S := Ioo A B
  let p := projection F u x h
  let : ContractibleSpace S := (convex_Ioo A B).contractibleSpace ⟨t₀.val,t₀.property⟩
  let sections := sectionMap p A B arc HA HL
  have Hproj (j : J) (t : S) : S.restrictPreimage p (sections j t) = t :=
    Subtype.ext (HL j t.val (Ioo_subset_Icc_self t.property))
  have Hcover (y : p ⁻¹' S) : ∃ j, JoinedIn ((S.restrictPreimage p) ⁻¹' {S.restrictPreimage p y}) y
      (sections j (S.restrictPreimage p y)) := by
    obtain ⟨j,HJ⟩ := HS (S.restrictPreimage p y) y.val rfl
    exact ⟨j,(RegularComponentTransport.joinedIn_restrictPreimage_iff p S (S.restrictPreimage p y)
      y (sections j (S.restrictPreimage p y)) rfl (Hproj _ _)).mpr HJ⟩
  have HP := FlatAffineShiftedSlice.projection_proper F u x h
  have HAB := t₀.property.1.trans t₀.property.2
  obtain ⟨C,HC,HF⟩ := FlatAffineRegularSliceCharts.exists_charts F u x h hh A B HR
  let piece := FiberSectionCover.piece (S.restrictPreimage p) sections
  have Hcl (j : J) : IsClopen (piece j) :=
    FiberSectionCover.isClopen_piece (S.restrictPreimage p) sections C HC HF (HP.restrictPreimage S) Hproj j
  let D : ComponentSlabCover.InteriorData p A B J := {
    piece := piece
    closed j := (Hcl j).isClosed
    cover := FiberSectionCover.cover (S.restrictPreimage p) sections Hcover
    paths := FiberSectionCover.paths (S.restrictPreimage p) sections C HC HF (HP.restrictPreimage S) Hproj
    arc := arc
    continuous_arc := HA
    arc_mem j t := ⟨sections j t,FiberSectionCover.section_mem_piece (S.restrictPreimage p) sections Hproj j t,rfl⟩
    level_left j := HL j A ⟨le_rfl,HAB.le⟩
    level_right j := HL j B ⟨HAB.le,le_rfl⟩
    limit_left j := (FiberSectionCover.isConnected_ambient_endpoint p sections C HC HF HP Hproj HAB j).isPreconnected
    limit_right j := (FiberSectionCover.isConnected_ambient_endpoint_right p sections C HC HF HP Hproj HAB j).isPreconnected }
  refine ⟨D,Hcl,fun _ _ => rfl,?_⟩
  intro i j
  have HE := FiberSectionCover.overlap_iff_sample (S.restrictPreimage p) sections C HC HF (HP.restrictPreimage S) Hproj t₀ i j
  have HJ := RegularComponentTransport.joinedIn_restrictPreimage_iff p S t₀ (sections i t₀) (sections j t₀) (Hproj _ _) (Hproj _ _)
  have HK := FlatAffineShiftedSlice.joined_fiber_iff F u x h hh t₀.val (arc i t₀.val) (arc j t₀.val)
    (HL i t₀.val (Ioo_subset_Icc_self t₀.property)) (HL j t₀.val (Ioo_subset_Icc_self t₀.property))
  exact HE.trans (HJ.trans HK)

end LeanCanny.Connectivity.FlatAffineRegularSectionSaturation
