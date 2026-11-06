/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialJointDescriptorLift
/-! # Genuine guarded two-label feasibility in the actual joint stratum -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialJointFeasibility
open LeanCanny.Encoding Set
open FormulaSignSlotRadialJointDescriptorGeometry

noncomputable def Feasible (H : List Bool) : Prop :=
  ∃ k : ℕ, ∃ x : FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H k),
    FormulaSignSlotRadialJointStratumLabels.BothLabels _ x ∧
    (anchor _ x).val.val ∈ FormulaSignSlotRadialParameterGrid.grid
      (FormulaSignSlotRadialJointStratumLabels.source true _) (center _ x) (radius _ x) ∧
    ∀ t ∈ Ioo 0 (bound _ x), t ∉ FormulaSignSlotRadialBranchCuts.cuts
      (FormulaSignSlotRadialJointStratumLabels.source true _) (center _ x)

end LeanCanny.Connectivity.FormulaSignSlotRadialJointFeasibility
