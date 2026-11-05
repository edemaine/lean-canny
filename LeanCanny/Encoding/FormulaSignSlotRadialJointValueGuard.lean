/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCenter
public import LeanCanny.Encoding.FormulaSignSlotRadialRetainedValueGuards
/-! # Actual value-cut selection on the one joint sampler packet

All coefficient, nonzero and trailing-index guards read the literal center
in the first source block. This does not impose interval cut avoidance or
associate a projected lift with a candidate component.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointSample
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Algebra LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "HN" => FormulaSignSlotRadialJointLayout.dimension_unary
local notation "HT" => FormulaSignSlotRadialJointCore.equation_FP
local notation "HA" => FormulaSignSlotRadialJointCore.scope
local notation "HR" => IntegralMixedOriginalRegularSource.radius_binary radius_binary
attribute [local irreducible] radius FormulaSignSlotRadialJointCore.equation
  FormulaSignSlotRadialJointLayout.dimension IntegralMixedPhysicalMarkedPlan.bank
  FormulaSignSlotRadialValueCertificate.polynomial FormulaSignSlotRadialCenterValueFamily.Guards
  slot context

noncomputable def valueIndex (p : List Bool) := Nat.fromBitsLE (slot 3 (context p))
noncomputable def valueQuery (p : List Bool) :=
  FormulaSignSlotRadialRetainedValueGuards.query (context p) (word p) (valueIndex p)
theorem valueIndex_binary : BinaryFn valueIndex := by
  have HS : (fun p => slot 3 (context p)) ∈ FP := mem_FP_comp (f := context) (g := slot 3) context_FP (slot_FP 3)
  exact BinaryFn.fromBits HS
theorem valueQuery_FP : valueQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair context_FP word_FP) valueIndex_binary.bits_mem_FP
noncomputable def ValueGuard (p : List Bool) :=
  FormulaSignSlotRadialRetainedValueGuards.Guards HN HT HA HR false valueContext centerRefs (valueQuery p)
theorem value_guard_evaluator : SpaceFunction (fun p => [decide (ValueGuard p)]) :=
  (FormulaSignSlotRadialRetainedValueGuards.evaluator HN HT HA HR false valueContext centerRefs
    valueContext_FP centerRefs_FP).precompose valueQuery valueQuery_FP

noncomputable def ValueMeaning (p : List Bool) (hv : Valid p) (ell : ℕ) : Prop :=
  FormulaSignSlotRadialCenterValueFamily.Guards (FormulaSignSlotRadialJointLayout.source true (header p))
    (FormulaSignSlotRadialJointGeometry.center (header p) (values p hv))
    (fun i => FormulaSignSlotRadialCenterValueLayout.tau (valueContext (context p)) i.val)
    (fun i => FormulaSignSlotRadialCenterValueLayout.degree (valueContext (context p)) i.val) ∧
  FormulaSignSlotRadialValueCertificate.polynomial (FormulaSignSlotRadialJointLayout.source true (header p))
    (FormulaSignSlotRadialJointGeometry.center (header p) (values p hv)) ≠ 0 ∧
  ell = (FormulaSignSlotRadialValueCertificate.polynomial (FormulaSignSlotRadialJointLayout.source true (header p))
    (FormulaSignSlotRadialJointGeometry.center (header p) (values p hv))).natTrailingDegree

theorem value_guard_actual (p : List Bool) (hv : Valid p) :
    ValueGuard p ↔ ValueMeaning p hv (valueIndex p) := by
  have HW : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input HN HT HA HR false) (context p) (word p) := full_valid p hv
  have HC : (fun i : Fin (FormulaSignSlotSource.dimension (FormulaSignSlotRadialJointLayout.source true (header p))) =>
      FormulaSignSlotRadialRetainedValueTest.center HN HT HA HR false centerRefs
        (context p) (word p) HW i.val) =
      FormulaSignSlotRadialJointGeometry.center (header p) (values p hv) := by
    funext i
    exact retained_center p hv i
  have HE := FormulaSignSlotRadialRetainedValueGuards.guards_actual HN HT HA HR false
    valueContext centerRefs (context p) (word p) HW (valueIndex p)
  have HO : FormulaSignSlotRadialCenterValueLayout.original (valueContext (context p)) =
      FormulaSignSlotRadialJointLayout.source true (header p) := by
    simp only [valueContext, FormulaSignSlotRadialCenterValueLayout.original, pairFst_pair,
      radialContext, header_context]
  rw [HO] at HE
  rw [HC] at HE
  exact HE

end LeanCanny.Encoding.FormulaSignSlotRadialJointSample
