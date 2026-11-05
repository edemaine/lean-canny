/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGeometry
public import LeanCanny.Connectivity.AuxiliaryCandidateComponentCover
/-! # Joint-source paths preserve each actual closed candidate component

This is a geometric projection theorem. It does not supply a native
cross-source component-membership decider.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointComponentTransport
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Algebra LeanCanny.ETR
open FormulaSignSlotRadialJointLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialJointCore.equation dimension
  FormulaSignSlotCircularBoundedCover.root ClosedFormulaGateMetadata.dimension
  ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom ClosedFormulaGateMetadata.kind
local notation "X" u => AuxiliaryCandidateComponentCover.Space dimension FormulaSignSlotRadialJointCore.equation u

theorem core_root (u : List Bool) (x : X u) :
    (FormulaSignSlotRadialJointCore.equation u).eval (Formula.extend x.val) = 0 := by
  have HX := x.property
  change (AuxiliaryTiltedTerm.polynomial (dimension u) (FormulaSignSlotRadialJointCore.equation u)).eval x.val = 0 at HX
  rw [AuxiliaryCandidateComponentCover.evaluation] at HX
  exact HX

noncomputable def project (side : Bool) (u : List Bool) (x : X u) :
    FormulaSignSlotCircularBoundedCover.Source (source side u) :=
  FormulaSignSlotRadialJointGeometry.closedPoint side u (Formula.extend x.val) (core_root u x)

theorem coordinate_lt (side : Bool) (u : List Bool) (i : Fin (circleCount side u)) :
    column (if side then 1 else 0) i.val < dimension u :=
  column_lt u _ _ (by cases side <;> decide) (i.isLt.trans_le (circle_lt_slots side u))

theorem project_coordinate (side : Bool) (u : List Bool) (x : X u) (i : Fin (circleCount side u)) :
    (project side u x).val i = x.val ⟨column (if side then 1 else 0) i.val, coordinate_lt side u i⟩ := by
  change Formula.extend x.val (column (if side then 1 else 0) i.val) = _
  simp only [Formula.extend, dite_eq_left (coordinate_lt side u i)]

theorem continuous_project (side : Bool) (u : List Bool) : Continuous (project side u) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun x : X u => (project side u x).val i)
  have HE : (fun x : X u => (project side u x).val i) =
      (fun x : X u => x.val ⟨column (if side then 1 else 0) i.val, coordinate_lt side u i⟩) :=
    funext (fun x => project_coordinate side u x i)
  rw [HE]
  exact (continuous_apply _).comp continuous_subtype_val

theorem joined_project (side : Bool) (u : List Bool) (x y : X u)
    (h : JoinedIn Set.univ x y) : JoinedIn Set.univ (project side u x) (project side u y) :=
  (h.map (continuous_project side u).continuousOn).mono (Set.subset_univ _)

theorem label_retained (side : Bool) (u : List Bool)
    (i : Vertex (CanonicalAuxiliaryCandidateCover.width (source side u)))
    (hi : CanonicalAuxiliaryCandidateLabelLock.Good (source side u) i) (x y : X u)
    (hx : JoinedIn Set.univ (CanonicalAuxiliaryCandidateLabelLock.closedSample (source side u) i hi)
      (project side u x)) (hxy : JoinedIn Set.univ x y) :
    JoinedIn Set.univ (CanonicalAuxiliaryCandidateLabelLock.closedSample (source side u) i hi)
      (project side u y) := hx.trans (joined_project side u x y hxy)

end LeanCanny.Encoding.FormulaSignSlotRadialJointComponentTransport
