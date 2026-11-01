/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotComponentMaxima
public import LeanCanny.Connectivity.ClopenPathCover
public import Mathlib.Topology.Order.LocalExtr
/-! # Boundary maxima are local extrema on the actual radial fiber

A clopen label in the positive-margin locus remains the same label at every
positive maximum. Its openness makes this a local extremum on the whole fiber.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotLocalMaxima
open Set Filter LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotMarginProjection FormulaSignSlotMarginMaxima
open FormulaSignSlotComponentMaxima
open scoped Topology Classical

theorem ambient_open (c : List Bool) (s : Set (Positive c)) (hs : IsOpen s) :
    IsOpen (ambient c s) :=
  (isOpen_lt continuous_const (continuous_value c)).isOpenMap_subtype_val s hs

theorem local_maximum (c : List Bool) (s : Set (Positive c)) (hs : IsOpen s)
    (center : Fin (FormulaSignSlotSource.dimension c) → ℝ) (r : ℝ)
    (y : Source c) (hy : y∈ambient c s)
    (HM : IsMaxOn (value c) (constrained c s center r) y) :
    IsLocalMaxOn (value c) (sourceSphere c center r) y := by
  have HA : ambient c s∈𝓝[sourceSphere c center r] y :=
    mem_nhdsWithin_of_mem_nhds ((ambient_open c s hs).mem_nhds hy)
  filter_upwards [HA,self_mem_nhdsWithin] with z hz hzS
  exact HM ⟨hzS,subset_closure hz⟩

theorem cover_boundary_maxima (c : List Bool) {I : Type*}
    (C : ClopenPathCover (Positive c) I) (i : I)
    (x : Source c) (hx : x∈closure (ambient c (C.piece i)))
    (hn : x∉ambient c (C.piece i)) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ ∃ y : Source c,
      y∈ambient c (C.piece i) ∧ y∈sourceSphere c (projection c x).val r ∧
      IsLocalMaxOn (value c) (sourceSphere c (projection c x).val r) y ∧
      0 < value c y := by
  obtain ⟨r,hr,hεr,y,hy,hyS,HM,HP⟩ := arbitrarily_small_maxima c (C.piece i)
    (C.clopen i).isClosed x hx hn ε hε
  exact ⟨r,hr,hεr,y,hy,hyS,local_maximum c (C.piece i) (C.clopen i).isOpen _ r y hy HM,HP⟩

end LeanCanny.Connectivity.FormulaSignSlotLocalMaxima
