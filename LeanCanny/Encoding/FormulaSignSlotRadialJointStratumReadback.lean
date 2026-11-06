/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCorePoint
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumLift
public import LeanCanny.Connectivity.FormulaSignSlotRadialJointDescriptorGeometry
/-! # The core-to-stratum lift retains the complete radial tuple -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointStratumReadback
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.ETR
open FormulaSignSlotRadialJointDescriptorGeometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] FormulaSignSlotSource.dimension
  FormulaSignSlotMargin.initialDimension FormulaSignSlotMargin.initialPolynomial

private theorem radial_values (q : List Bool) (v : ℕ → ℝ)
    (h : (FormulaSignSlotRadialJointCore.equation q).eval v = 0) :
    (FormulaSignSlotRadialJointGeometry.radialPoint q v h).val.val =
      FormulaSignSlotRadialJointGeometry.spatialPoint q v := rfl

variable (c u : List Bool) (hc : FormulaSignSlotRadialJointStratum.header c = u)
  (env : ℕ → ℝ) (h0 : (FormulaSignSlotRadialJointCore.equation u).eval env = 0)
  (y : FormulaSignSlotRadialJointStratumLabels.Space c)
  (hy : HEq (FormulaSignSlotRadialJointStratum.oldPoint c y.val)
    (FormulaSignSlotRadialJointCorePoint.ofEnvironment u env h0).val)

include hc h0 hy

theorem coordinate (i : ℕ) (hi : i < FormulaSignSlotRadialJointLayout.dimension u) :
    environment c y i = env i := by
  subst u
  have H : FormulaSignSlotRadialJointStratum.oldPoint c y.val =
      (fun j : Fin (FormulaSignSlotRadialJointLayout.dimension (FormulaSignSlotRadialJointStratum.header c)) => env j.val) :=
    eq_of_heq hy
  change Formula.extend (FormulaSignSlotRadialJointStratum.oldPoint c y.val) i = env i
  simp only [Formula.extend, dite_eq_left hi]
  exact congrFun H ⟨i,hi⟩

theorem radius_value : radius c y = env
    (FormulaSignSlotRadialJointLayout.radiusVariable (FormulaSignSlotRadialJointStratum.header c)) := by
  simpa only [radius, FormulaSignSlotRadialJointGeometry.parameter] using
    coordinate c u hc env h0 y hy
      (FormulaSignSlotRadialJointLayout.radiusVariable (FormulaSignSlotRadialJointStratum.header c))
      ((FormulaSignSlotRadialJointLayout.radiusVariable_lt _).trans_eq
        (congrArg FormulaSignSlotRadialJointLayout.dimension hc))

theorem bound_value : bound c y = env FormulaSignSlotRadialJointLayout.boundVariable :=
  coordinate c u hc env h0 y hy _
    ((FormulaSignSlotRadialJointLayout.boundVariable_lt _).trans_eq
      (congrArg FormulaSignSlotRadialJointLayout.dimension hc))

theorem center_value : center c y =
    FormulaSignSlotRadialJointGeometry.center (FormulaSignSlotRadialJointStratum.header c) env := by
  funext i
  change environment c y (FormulaSignSlotRadialJointLayout.column 0 i.val) =
    env (FormulaSignSlotRadialJointLayout.column 0 i.val)
  apply coordinate c u hc env h0 y hy
  apply (FormulaSignSlotRadialJointLayout.column_lt _ 0 _ (by decide) ?_).trans_eq
    (congrArg FormulaSignSlotRadialJointLayout.dimension hc)
  have H := FormulaSignSlotRadialJointLayout.formal_le_slots (FormulaSignSlotRadialJointStratum.header c)
  have HI := i.isLt
  change i.val < FormulaSignSlotRadialJointLayout.centerCount (FormulaSignSlotRadialJointStratum.header c) at HI
  change FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c) +
    (FormulaSignSlotRadialJointLayout.centerCount (FormulaSignSlotRadialJointStratum.header c) + 1) ≤ _ at H
  omega

theorem anchor_value : (anchor c y).val.val =
    FormulaSignSlotRadialJointGeometry.spatialPoint (FormulaSignSlotRadialJointStratum.header c) env := by
  have HA : (anchor c y).val.val = FormulaSignSlotRadialJointGeometry.spatialPoint
      (FormulaSignSlotRadialJointStratum.header c) (environment c y) :=
    radial_values _ _ (FormulaSignSlotRadialJointDescriptorGeometry.core_zero c y)
  apply HA.trans
  funext i
  change environment c y (FormulaSignSlotRadialJointLayout.column 2 i.val) =
    env (FormulaSignSlotRadialJointLayout.column 2 i.val)
  apply coordinate c u hc env h0 y hy
  apply (FormulaSignSlotRadialJointLayout.column_lt _ 2 _ (by decide) ?_).trans_eq
    (congrArg FormulaSignSlotRadialJointLayout.dimension hc)
  have H := FormulaSignSlotRadialJointLayout.formal_le_slots (FormulaSignSlotRadialJointStratum.header c)
  have HI := i.isLt
  change FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c) +
    (FormulaSignSlotRadialJointLayout.centerCount (FormulaSignSlotRadialJointStratum.header c) + 1) ≤ _ at H
  omega

theorem grid_iff :
    (anchor c y).val.val ∈ FormulaSignSlotRadialParameterGrid.grid
      (FormulaSignSlotRadialJointStratumLabels.source true c) (center c y) (radius c y) ↔
    FormulaSignSlotRadialJointGeometry.spatialPoint u env ∈ FormulaSignSlotRadialParameterGrid.grid
      (FormulaSignSlotRadialJointLayout.source true u) (FormulaSignSlotRadialJointGeometry.center u env)
      (FormulaSignSlotRadialJointGeometry.parameter u env) := by
  subst u
  rw [anchor_value c _ rfl env h0 y hy, center_value c _ rfl env h0 y hy,
    radius_value c _ rfl env h0 y hy]
  rfl

theorem cut_free_iff :
    (∀ t ∈ Set.Ioo 0 (bound c y), t ∉ FormulaSignSlotRadialBranchCuts.cuts
      (FormulaSignSlotRadialJointStratumLabels.source true c) (center c y)) ↔
    (∀ t ∈ Set.Ioo 0 (env FormulaSignSlotRadialJointLayout.boundVariable),
      t ∉ FormulaSignSlotRadialBranchCuts.cuts (FormulaSignSlotRadialJointLayout.source true u)
        (FormulaSignSlotRadialJointGeometry.center u env)) := by
  subst u
  rw [bound_value c _ rfl env h0 y hy, center_value c _ rfl env h0 y hy]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialJointStratumReadback
