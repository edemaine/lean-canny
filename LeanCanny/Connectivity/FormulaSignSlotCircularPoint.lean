/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateNonempty

/-! # Literal original coordinates of a closed circular source point

Proper projection, circular retraction and the margin graph retain the old
coordinates. A point in a labeled closed source piece projects into the
positive Boolean piece carrying the same label.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotCircularBoundedCover
open Set ETR LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] root FormulaSignSlotMargin.prepared FormulaSignSlotSource.dimension
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count Input.field

noncomputable def originalIndex (c : List Bool) (i : Fin (FormulaSignSlotCircularInterior.description c).dimension) :
    Fin (BoundedMonotoneGateSource.total ClosedFormulaGateTruth.F (root c)) :=
  ⟨i.val,by
    have HI : i.val<ClosedFormulaGateTruth.F.dimension (root c) := by rw [root_dimension]; exact i.isLt
    change i.val<ClosedFormulaGateTruth.F.dimension (root c)+2*ClosedFormulaGateTruth.F.count (root c)+
      ClosedFormulaGateTruth.F.count (root c)+2*ClosedFormulaGateTruth.F.count (root c)
    omega⟩

private theorem equality_coordinate {d e : Description} (H : d=e) (x : d.realization) (i : ℕ)
    (hd : i<d.dimension) (he : i<e.dimension) :
    (FormulaSignSlotMarginProjection.equalityHomeomorph H x).val ⟨i,he⟩=x.val ⟨i,hd⟩ := by
  cases H
  rfl

theorem projection_coordinate (c : List Bool) (y : Source c)
    (i : Fin (FormulaSignSlotCircularInterior.description c).dimension) :
    (projection c y).val i=y.val (originalIndex c i) := by
  let z:=ClosedFormulaBoundedGate.projection (FormulaSignSlotCircularInterior.closed c) (root c)
    (root_formula c) (root_scope c) y
  have HR : i.val<ClosedFormulaGateTruth.F.dimension (root c) := by rw [root_dimension]; exact i.isLt
  have HE:=equality_coordinate (target_eq c) z i.val HR i.isLt
  have HO:=congrFun (ClosedFormulaBoundedFrontier.projection_coordinates
    (FormulaSignSlotCircularInterior.closed c) (root c) (root_formula c) (root_scope c) y) ⟨i.val,HR⟩
  exact HE.trans HO

noncomputable def positivePoint (c : List Bool) (y : Source c) : FormulaSignSlotComponentMaxima.Positive c :=
  FormulaSignSlotCircularInterior.projection c (projection c y)

noncomputable def projectedPoint (c : List Bool) (y : Source c) : FormulaSignSlotMarginProjection.Target c :=
  FormulaSignSlotMarginProjection.projection c (positivePoint c y).val

noncomputable def projectedIndex (c : List Bool) (i : Fin (FormulaSignSlotSource.dimension c)) :=
  originalIndex c (Fin.castAdd 2 (FormulaSignSlotMarginProjection.oldIndex c i))

theorem projectedPoint_coordinate (c : List Bool) (y : Source c) (i : Fin (FormulaSignSlotSource.dimension c)) :
    (projectedPoint c y).val i=y.val (projectedIndex c i) := by
  rw [projectedPoint,FormulaSignSlotMarginProjection.projection_coordinate]
  unfold positivePoint projectedIndex
  rw [FormulaSignSlotCircularInterior.projection_coordinate,projection_coordinate]

theorem projectedPoint_mem (c : List Bool) {I : Type*} [Finite I]
    (p : I→Set (Source c)) (hcover : ∀ y,∃ i,y∈p i) (haccess : ∀ i,FrontierCover.Accessible (p i))
    (i : I) (y : Source c) (hy : y∈p i) :
    (projectedPoint c y).val∈FormulaSignSlotRadialAccess.projectedPiece c
      ((positiveCover c p hcover haccess).piece i) := by
  have HC : projection c y∈(closedCover c p hcover haccess).piece i := ⟨i,.refl,y,hy,rfl⟩
  have HP : positivePoint c y∈(positiveCover c p hcover haccess).piece i :=
    (closedCover c p hcover haccess).mem_of_joined i HC
      (FormulaSignSlotCircularInterior.fiber_joined c (projection c y))
  exact ⟨(positivePoint c y).val,⟨positivePoint c y,HP,rfl⟩,rfl⟩

end LeanCanny.Connectivity.FormulaSignSlotCircularBoundedCover
