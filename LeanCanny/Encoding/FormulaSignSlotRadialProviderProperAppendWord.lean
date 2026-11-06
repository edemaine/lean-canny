/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendTuple
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendWord
/-! # A fresh own full word realizes every coordinate of the proper-child tuple -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedRunObservation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem sample_bank (bank : IntegralFramedBankQuery.Bank) (c root : List Bool)
    (hr : pairFst (bank.key c)=root)
    (hc : prefixLength bank.parameters (bank.key c)=(bank.plan.rules root).length)
    (u : ℕ→ℝ)
    (hu : (ofCommands (initial bank.parameters bank.plan root) (bank.plan.rules root)
      (by have H := bank.plan.room root;omega)).Roots u) :
    FormulaSignSlotRadialProviderRetainedAppend.JointSampled bank c u :=
  IntegralFramedPhysicalSquare.exists_full_observation bank.parameters bank.plan bank.data
    bank.nodes bank.factor bank.seed bank.bounds bank.key bank.positive c root hr hc u hu

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side

noncomputable def Sampled (u : ℕ→ℝ) :=
  FormulaSignSlotRadialProviderRetainedAppend.JointSampled B
    (FormulaSignSlotRadialProviderRecordPrefix.context r) u

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.JointSampled fullObservation

theorem sample_full_tuple (u : ℕ→ℝ)
    (hu : (fullObservation old hv hd left right R side).Roots u) : Sampled old hv hd left right R side u := by
  unfold fullObservation at hu
  unfold Sampled
  have HC : prefixLength (B).parameters ((B).key (FormulaSignSlotRadialProviderRecordPrefix.context r))=
      ((B).plan.rules r).length :=
    (FormulaSignSlotRadialProviderRecordPrefix.full_prefix r).trans (full_rules_length r).symm
  exact sample_bank B (FormulaSignSlotRadialProviderRecordPrefix.context r) r
    (FormulaSignSlotRadialProviderRecordPrefix.key_root r) HC u hu

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
