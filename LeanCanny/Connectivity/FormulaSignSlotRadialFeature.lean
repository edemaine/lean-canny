/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotLocalMaxima
public import LeanCanny.ETR.SquaredNormTerm
public import LeanCanny.Geometry.SquaredDistanceLinearization
/-! # One native quadratic feature on the actual bounded margin source

The graph is homeomorphic to the existing source, retaining every old witness
and component label. Both the margin objective and radial constraint become
literal coordinate/affine expressions in this one initial source.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialFeature
open ETR Set LeanCanny.Encoding LeanCanny.Computation LeanCanny.Geometry
open FormulaSignSlotMarginProjection FormulaSignSlotMarginMaxima ClosedFormulaGateTruth
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  ClosedFormulaGateMetadata.atom ClosedFormulaGateMetadata.kind FormulaSignSlotMargin.prepared

theorem source_scope (c : List Bool) : (FormulaSignSlotMargin.initialPolynomial c).arity≤
    FormulaSignSlotMargin.initialDimension c :=
  BoundedMonotoneGateSource.polynomial_arity F (root c) (ClosedFormulaGateTruth.source_scope (root c))

theorem old_dimension_le (c : List Bool) : FormulaSignSlotSource.dimension c≤FormulaSignSlotMargin.initialDimension c := by
  have H := (objectiveIndex c).isLt
  change FormulaSignSlotSource.dimension c < FormulaSignSlotMargin.initialDimension c at H
  exact H.le

noncomputable def description (c : List Bool) : Description :=
  TermCoordinateGraph.description (FormulaSignSlotMargin.initialDimension c)
    (.eqZero (FormulaSignSlotMargin.initialPolynomial c)) (SquaredNormTerm.term (FormulaSignSlotSource.dimension c))

noncomputable abbrev Lifted (c : List Bool) := (description c).realization

noncomputable def homeomorph (c : List Bool) : Lifted c ≃ₜ Source c :=
  TermCoordinateGraph.homeomorph _ _ _ (source_scope c)
    ((SquaredNormTerm.scope _).trans (old_dimension_le c))

theorem old_coordinate (c : List Bool) (y : Lifted c) (i : Fin (FormulaSignSlotMargin.initialDimension c)) :
    (homeomorph c y).val i=y.val (Fin.castAdd 1 i) := rfl

noncomputable def oldTuple (c : List Bool) (y : Lifted c) := (projection c (homeomorph c y)).val

theorem oldTuple_coordinate (c : List Bool) (y : Lifted c) (i : Fin (FormulaSignSlotSource.dimension c)) :
    oldTuple c y i=y.val (Fin.castAdd 1 (oldIndex c i)) := by
  rw [oldTuple,projection_coordinate,old_coordinate]

theorem feature_coordinate (c : List Bool) (y : Lifted c) :
    y.val (Fin.last (FormulaSignSlotMargin.initialDimension c))=
      SquaredDistanceLinearization.feature (oldTuple c y) := by
  have H := TermCoordinateGraph.objective_coordinate _ _ _ (source_scope c)
    ((SquaredNormTerm.scope _).trans (old_dimension_le c)) y
  rw [SquaredNormTerm.eval] at H
  apply H.trans
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [oldTuple,projection_coordinate]
  have HI : i.val < FormulaSignSlotMargin.initialDimension c := i.isLt.trans_le (old_dimension_le c)
  simp only [Formula.extend,dite_eq_left HI]
  rfl

theorem radial_affine (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ) (y : Lifted c) :
    SquaredDistanceLinearization.affine center
      (y.val (Fin.last (FormulaSignSlotMargin.initialDimension c))) (oldTuple c y)=
        SquaredDistanceFibers.value center (oldTuple c y) := by
  rw [feature_coordinate,SquaredDistanceLinearization.affine_feature]

theorem margin_coordinate (c : List Bool) (y : Lifted c) :
    y.val (Fin.castAdd 1 (objectiveIndex c))=value c (homeomorph c y) := rfl

noncomputable def liftedSphere (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (r : ℝ) : Set (Lifted c) := homeomorph c ⁻¹' sourceSphere c center r

theorem sphere_affine (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (r : ℝ) (y : Lifted c) : y∈liftedSphere c center r ↔
      SquaredDistanceLinearization.affine center
        (y.val (Fin.last (FormulaSignSlotMargin.initialDimension c))) (oldTuple c y)=r := by
  rw [radial_affine]
  rfl

theorem local_maximum (c : List Bool) (center : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (r : ℝ) (y : Lifted c) (hy : y∈liftedSphere c center r)
    (HM : IsLocalMaxOn (value c) (sourceSphere c center r) (homeomorph c y)) :
    IsLocalMaxOn (fun z : Lifted c => z.val (Fin.castAdd 1 (objectiveIndex c))) (liftedSphere c center r) y :=
  HM.comp_continuousOn Subset.rfl (homeomorph c).continuous.continuousOn hy

end LeanCanny.Connectivity.FormulaSignSlotRadialFeature
