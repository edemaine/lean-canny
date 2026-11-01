/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotMarginProjection
public import LeanCanny.Geometry.SquaredDistanceProper
public import LeanCanny.Geometry.ConnectedSlabLimit
/-! # Proper radial sweeps retain the original boundary point

Squared distance uses only retained old coordinates. Properness follows from
the actual bounded witness compiler, including all of its witness coordinates.
A zero-radius endpoint projects to the prescribed old tuple; no choice of an
absolute algebraic root or lifting of a different parent is involved.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialSweep
open Set LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotMarginProjection
open scoped BigOperators

noncomputable def radial (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (y : Source c) : ℝ := SquaredDistanceFibers.value center (projection c y).val

theorem proper_radial (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ) :
    IsProperMap (radial c center) := by
  have HT : IsProperMap (Subtype.val : Target c → (Fin (FormulaSignSlotSource.dimension c) → ℝ)) :=
    (FormulaSignPartition.closed_holds (FormulaSignSlotSource.envelope_closed c) _).isProperMap_subtypeVal
  exact (SquaredDistanceFibers.proper_value center).comp (HT.comp (proper_projection c))

theorem radial_coordinates (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (y : Source c) : radial c center y=∑ i, (y.val (oldIndex c i)-center i)^2 := by
  unfold radial SquaredDistanceFibers.value
  simp only [projection_coordinate]

theorem zero_iff (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (y : Source c) : radial c center y=0 ↔ (projection c y).val=center :=
  SquaredDistanceFibers.zero_iff center (projection c y).val

theorem endpoint_coordinates (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (s : Set (Source c)) {y : Source c} (hy : y∈closure s ∩ radial c center ⁻¹' {0}) :
    ∀ i, y.val (oldIndex c i)=center i := by
  have H := (zero_iff c center y).mp hy.2
  intro i
  rw [← projection_coordinate, H]

theorem connected_endpoint (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (s : Set (Source c)) (b : ℝ) (hb : 0 < b) (hs : s⊆radial c center ⁻¹' Ioo 0 b)
    (hc : ∀ r : Ioo 0 b, IsConnected (ConnectedSlabLimit.tail (radial c center) (a:=0) s r.val)) :
    IsConnected (closure s∩radial c center ⁻¹' {0}) :=
  ConnectedSlabLimit.isConnected_endpoint (radial c center) (proper_radial c center) hb hs hc

theorem compact_endpoint (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (s : Set (Source c)) : IsCompact (closure s∩radial c center ⁻¹' {0}) :=
  ConnectedSlabLimit.isCompact_endpoint (radial c center) (proper_radial c center)

end LeanCanny.Connectivity.FormulaSignSlotRadialSweep
