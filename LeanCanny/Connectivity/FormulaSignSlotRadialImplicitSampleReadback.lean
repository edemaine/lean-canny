/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridSelection
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGridRetention
/-! # Native OWN tests and the actual stratum retain the same radial tuple -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialImplicitSampleReadback
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
local notation "env" => FormulaSignSlotRadialImplicitGridTest.env
local notation "geom" => FormulaSignSlotRadialJointDescriptorGeometry.environment
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension FormulaSignSlotMargin.initialPolynomial

private theorem extend_heq {n m : ℕ} (h : n=m) (a : Fin n → ℝ) (b : Fin m → ℝ) (ha : HEq a b) :
    IntegralMixedFramedBankObservation.extend a = Formula.extend b := by
  cases h
  have H : a=b := eq_of_heq ha
  subst b
  rfl

variable (c Gamma w : List Bool) (hw : SquareSampleCompleteVertices.Valid F (pair c Gamma) w)
  (x : FormulaSignSlotRadialJointStratumLabels.Space c)
  (hx : HEq (SquareSampleCompleteVertices.candidate F (pair c Gamma) w hw).val x.val)
include hx

theorem coordinate (i : ℕ) (hi : i < FormulaSignSlotRadialJointStratum.oldArity c) :
    env (pair c Gamma) w hw i = geom c x i := by
  have HN : (F).count (pair c Gamma) = FormulaSignSlotRadialJointStratum.arity c := by
    change FormulaSignSlotRadialJointStratum.arity (ImplicitSourceGramGrid.header (pair c Gamma)) = _
    simp only [ImplicitSourceGramGrid.header,pairFst_pair]
  have HE := extend_heq HN (SquareSampleCompleteVertices.candidate F (pair c Gamma) w hw).val x.val hx
  change IntegralMixedFramedBankObservation.extend _ i = _
  rw [HE]
  have HF : i < FormulaSignSlotRadialJointStratum.arity c := by
    change i < FormulaSignSlotRadialJointStratum.oldArity c+1
    omega
  simp only [FormulaSignSlotRadialJointDescriptorGeometry.environment,Formula.extend,dite_eq_left HF,dite_eq_left hi]
  rfl

theorem center : FormulaSignSlotRadialJointGeometry.center (FormulaSignSlotRadialJointStratum.header c)
    (env (pair c Gamma) w hw) = FormulaSignSlotRadialJointDescriptorGeometry.center c x := by
  funext i
  change env (pair c Gamma) w hw (4*i.val) = geom c x (4*i.val)
  apply coordinate c Gamma w hw x hx
  apply FormulaSignSlotRadialJointLayout.column_lt _ 0 _ (by decide)
  have H := FormulaSignSlotRadialJointLayout.formal_le_slots (FormulaSignSlotRadialJointStratum.header c)
  have HI := i.isLt
  change i.val < FormulaSignSlotRadialJointLayout.centerCount (FormulaSignSlotRadialJointStratum.header c) at HI
  change FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c)+
    (FormulaSignSlotRadialJointLayout.centerCount (FormulaSignSlotRadialJointStratum.header c)+1) ≤ _ at H
  omega

theorem radius : FormulaSignSlotRadialJointGeometry.parameter (FormulaSignSlotRadialJointStratum.header c)
    (env (pair c Gamma) w hw) = FormulaSignSlotRadialJointDescriptorGeometry.radius c x :=
  coordinate c Gamma w hw x hx _ (FormulaSignSlotRadialJointLayout.radiusVariable_lt _)

theorem bound : env (pair c Gamma) w hw FormulaSignSlotRadialJointLayout.boundVariable =
    FormulaSignSlotRadialJointDescriptorGeometry.bound c x :=
  coordinate c Gamma w hw x hx _ (FormulaSignSlotRadialJointLayout.boundVariable_lt _)

theorem spatial : FormulaSignSlotRadialJointGeometry.spatialPoint (FormulaSignSlotRadialJointStratum.header c)
    (env (pair c Gamma) w hw) = FormulaSignSlotRadialJointGeometry.spatialPoint
      (FormulaSignSlotRadialJointStratum.header c) (geom c x) := by
  funext i
  apply coordinate c Gamma w hw x hx
  apply FormulaSignSlotRadialJointLayout.column_lt _ 2 _ (by decide)
  have H := FormulaSignSlotRadialJointLayout.formal_le_slots (FormulaSignSlotRadialJointStratum.header c)
  have HI := i.isLt
  change FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialJointStratum.header c)+
    (FormulaSignSlotRadialJointLayout.centerCount (FormulaSignSlotRadialJointStratum.header c)+1) ≤ _ at H
  omega

/-- Native grid acceptance refers to this prescribed actual stratum point. -/
theorem grid_iff : FormulaSignSlotRadialImplicitGridSelection.Holds (pair (pair c Gamma) w) ↔
    FormulaSignSlotRadialJointGridRetention.Grid c x := by
  rw [FormulaSignSlotRadialImplicitGridSelection.holds_packet_iff _ _ hw]
  have HH : FormulaSignSlotRadialImplicitGridTest.header (pair c Gamma) = FormulaSignSlotRadialJointStratum.header c := by
    simp only [FormulaSignSlotRadialImplicitGridTest.header,ImplicitSourceGramGrid.header,pairFst_pair]
  change (FormulaSignSlotRadialJointGeometry.spatialPoint _ _ ∈ FormulaSignSlotRadialParameterGrid.grid _ _ _) ↔ _
  rw [HH,spatial c Gamma w hw x hx,center c Gamma w hw x hx,radius c Gamma w hw x hx]
  rfl


/-- Every cut test uses the same center and interval endpoint as the actual point. -/
theorem cut_free_iff :
    (∀ r ∈ Set.Ioo 0 (env (pair c Gamma) w hw FormulaSignSlotRadialJointLayout.boundVariable),
      r ∉ FormulaSignSlotRadialBranchCuts.cuts (FormulaSignSlotRadialJointStratumLabels.source true c)
        (FormulaSignSlotRadialJointGeometry.center (FormulaSignSlotRadialJointStratum.header c)
          (env (pair c Gamma) w hw))) ↔
    ∀ r ∈ Set.Ioo 0 (FormulaSignSlotRadialJointDescriptorGeometry.bound c x),
      r ∉ FormulaSignSlotRadialBranchCuts.cuts (FormulaSignSlotRadialJointStratumLabels.source true c)
        (FormulaSignSlotRadialJointDescriptorGeometry.center c x) := by
  rw [center c Gamma w hw x hx,bound c Gamma w hw x hx]

end LeanCanny.Connectivity.FormulaSignSlotRadialImplicitSampleReadback
