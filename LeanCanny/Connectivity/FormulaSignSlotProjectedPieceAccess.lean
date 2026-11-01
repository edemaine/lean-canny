/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotBoundaryAccess
/-! # Accessible projected components of actual sign strata

Properness of the actual margin source lifts a specified old-coordinate
boundary point into the closure of the SAME source piece. Constructed radial
branches then attach it to that piece. Only an interior clopen path cover is
input; no boundary-accessibility or relative regularity premise remains.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotProjectedPieceAccess
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotMarginProjection FormulaSignSlotComponentMaxima FormulaSignSlotRadialAccess
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotMargin.initialDimension FormulaSignSlotSource.dimension
  FormulaSignSlotMargin.initialPolynomial

theorem closed_oldProjection (c : List Bool) :
    IsClosedMap (fun y : Source c => (projection c y).val) := by
  have HC : IsClosed {x : Fin (FormulaSignSlotSource.dimension c) → ℝ |
      (FormulaSignSlotSource.envelope c).Holds (Formula.extend x)} :=
    FormulaSignPartition.closed_holds (FormulaSignSlotSource.envelope_closed c) _
  have HV : IsClosedMap (Subtype.val : Target c → Fin (FormulaSignSlotSource.dimension c) → ℝ) :=
    HC.isClosedEmbedding_subtypeVal.isClosedMap
  exact HV.comp (proper_projection c).isClosedMap

theorem boundary_lift (c : List Bool) (C : Set (Positive c))
    (x : Fin (FormulaSignSlotSource.dimension c) → ℝ) (hx : x∈closure (projectedPiece c C)) :
    ∃ z : Source c, z∈closure (ambient c C) ∧ (projection c z).val=x := by
  have HF : Continuous (fun z : Source c => (projection c z).val) :=
    continuous_subtype_val.comp (proper_projection c).continuous
  rw [projectedPiece,(closed_oldProjection c).closure_image_eq_of_continuous HF] at hx
  exact hx

theorem accessible (c : List Bool) {I : Type*} (C : ClopenPathCover (Positive c) I) (i : I) :
    FrontierCover.Accessible (projectedPiece c (C.piece i)) := by
  intro x hx y hy
  by_cases HI : x∈projectedPiece c (C.piece i)
  · have H := (piece_paths c C i x HI y hy).mono (subset_insert x _)
    exact H
  · obtain ⟨z,HZ,HP⟩ := boundary_lift c (C.piece i) x hx
    have HN : z∉ambient c (C.piece i) := by
      intro H
      exact HI ⟨z,H,HP⟩
    rw [← HP]
    exact FormulaSignSlotBoundaryAccess.joined_boundary_piece c C i z HZ HN y hy
end LeanCanny.Connectivity.FormulaSignSlotProjectedPieceAccess
