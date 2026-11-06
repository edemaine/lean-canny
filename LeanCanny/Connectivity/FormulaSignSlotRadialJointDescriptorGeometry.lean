/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumLabels
public import LeanCanny.Encoding.FormulaSignSlotRadialJointRealization
/-! # The literal joint anchor gives the original radial descriptor

The grid and interval conditions refer to the actual joint coordinates.
Component membership supplies the selected original label.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialJointDescriptorGeometry
open LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] FormulaSignSlotTiltedRadialGrid.Q
  FormulaSignSlotCenteredRadialLimits.polynomial FormulaSignSlotSource.dimension
  FormulaSignSlotMargin.initialPolynomial
  FormulaSignSlotCircularBoundedCover.root
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom
  ClosedFormulaGateMetadata.kind Input.field FormulaView.normalize

private theorem radial_coordinate (q : List Bool) (env : ℕ → ℝ)
    (h : (FormulaSignSlotRadialJointCore.equation q).eval env = 0)
    (i : Fin (FormulaSignSlotMargin.initialDimension (FormulaSignSlotRadialJointLayout.source true q))) :
    (FormulaSignSlotTiltedRadialGrid.originalPositive _
      (FormulaSignSlotRadialJointGeometry.center q env) (FormulaSignSlotRadialJointGeometry.parameter q env)
      (FormulaSignSlotRadialJointGeometry.radialPoint q env h)).val.val i =
        env (FormulaSignSlotRadialJointLayout.column 2 i.val) := rfl

private theorem core_center (q : List Bool) (env : ℕ → ℝ)
    (h : (FormulaSignSlotRadialJointCore.equation q).eval env = 0) :
    FormulaSignSlotRadialJointGeometry.center q env =
      FormulaSignSlotRadialJointRealization.leftCenter q
        (FormulaSignSlotRadialJointGeometry.closedPoint false q env h) := by
  funext i
  rw [FormulaSignSlotRadialJointRealization.leftCenter_coordinate]
  rfl

noncomputable def environment (c : List Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c) : ℕ → ℝ :=
  Formula.extend (FormulaSignSlotRadialJointStratum.oldPoint c x.val)

theorem core_zero (c : List Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c) :
    (FormulaSignSlotRadialJointCore.equation (FormulaSignSlotRadialJointStratum.header c)).eval (environment c x) = 0 :=
  ((FormulaSignSlotRadialJointStratum.zero_iff c x.val).mp (FormulaSignSlotRadialJointStratumLabels.source_zero c x)).1

noncomputable def center (c : List Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c) : Fin (FormulaSignSlotSource.dimension (FormulaSignSlotRadialJointStratumLabels.source true c)) → ℝ := FormulaSignSlotRadialJointGeometry.center (FormulaSignSlotRadialJointStratum.header c) (environment c x)
noncomputable def radius (c : List Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c) : ℝ := FormulaSignSlotRadialJointGeometry.parameter (FormulaSignSlotRadialJointStratum.header c) (environment c x)
noncomputable def bound (c : List Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c) : ℝ := environment c x FormulaSignSlotRadialJointLayout.boundVariable
noncomputable def anchor (c : List Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c) :
    FormulaSignSlotTiltedRadialGrid.OldPositive (FormulaSignSlotRadialJointStratumLabels.source true c) (center c x) (radius c x) :=
  FormulaSignSlotRadialJointGeometry.radialPoint (FormulaSignSlotRadialJointStratum.header c) (environment c x) (core_zero c x)

theorem radius_bounds (c : List Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c) :
    0 < radius c x ∧ radius c x < bound c x :=
  FormulaSignSlotRadialJointCoreReadback.parameter_positive _ _ (core_zero c x)

theorem anchor_projection (c : List Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c) :
    CanonicalAuxiliaryCandidateLabelLock.positiveProjection (FormulaSignSlotRadialJointStratumLabels.source true c) (FormulaSignSlotRadialJointStratumLabels.project true c x) =
      FormulaSignSlotTiltedRadialGrid.originalPositive (FormulaSignSlotRadialJointStratumLabels.source true c) (center c x) (radius c x)
        (anchor c x) := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  have HA := (FormulaSignSlotRadialJointCoreReadback.zero_iff _ _).mp (core_zero c x) |>.2.2.2.2.1
  have HV := FormulaSignSlotRadialJointGeometry.positive_coordinate (FormulaSignSlotRadialJointStratumLabels.source true c) (FormulaSignSlotRadialJointStratumLabels.project true c x) i
  have HP : (FormulaSignSlotRadialJointStratumLabels.project true c x).val
      (FormulaSignSlotCircularBoundedCover.originalIndex _ (Fin.castAdd 2 i)) =
      environment c x (FormulaSignSlotRadialJointLayout.column 1 i.val) := rfl
  have HQ := radial_coordinate (FormulaSignSlotRadialJointStratum.header c) (environment c x)
    (core_zero c x) i
  exact HV.trans (HP.trans ((HA i.val i.isLt).symm.trans HQ.symm))

theorem center_left_projection (c : List Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c) :
    center c x = FormulaSignSlotRadialJointRealization.leftCenter
      (FormulaSignSlotRadialJointStratum.header c)
      (FormulaSignSlotRadialJointStratumLabels.project false c x) :=
  core_center _ _ (core_zero c x)

attribute [local irreducible] center radius bound anchor

noncomputable def descriptor (c : List Bool) (x : FormulaSignSlotRadialJointStratumLabels.Space c)
    (i : Vertex (CanonicalAuxiliaryCandidateCover.width (FormulaSignSlotRadialJointStratumLabels.source true c)))
    (hi : CanonicalAuxiliaryCandidateLabelLock.Good (FormulaSignSlotRadialJointStratumLabels.source true c) i)
    (hp : JoinedIn univ (CanonicalAuxiliaryCandidateLabelLock.closedSample (FormulaSignSlotRadialJointStratumLabels.source true c) i hi)
      (FormulaSignSlotRadialJointStratumLabels.project true c x))
    (hg : (anchor c x).val.val ∈ FormulaSignSlotRadialParameterGrid.grid
      (FormulaSignSlotRadialJointStratumLabels.source true c) (center c x) (radius c x))
    (hc : ∀ t ∈ Ioo 0 (bound c x), t ∉ FormulaSignSlotRadialBranchCuts.cuts
      (FormulaSignSlotRadialJointStratumLabels.source true c) (center c x)) :
    FormulaSignSlotCandidateRadialDescriptor.Descriptor (FormulaSignSlotRadialJointStratumLabels.source true c) i (center c x) where
  bound := bound c x
  bound_pos := lt_trans (radius_bounds c x).1 (radius_bounds c x).2
  parameter := ⟨radius c x, radius_bounds c x⟩
  anchor := anchor c x
  grid := hg
  cut_free := hc
  good := hi
  closedAnchor := FormulaSignSlotRadialJointStratumLabels.project true c x
  anchor_projection := anchor_projection c x
  anchor_component := hp

end LeanCanny.Connectivity.FormulaSignSlotRadialJointDescriptorGeometry
