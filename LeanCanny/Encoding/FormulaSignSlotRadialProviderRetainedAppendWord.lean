/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendTuple
public import LeanCanny.Encoding.IntegralFramedPhysicalExactVertex
/-! # A fresh own full word realizes the entire retained-child tuple -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedRunObservation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def JointSampled (B : IntegralFramedBankQuery.Bank) (c : List Bool) (u : ℕ→ℝ) : Prop :=
  ∃w,∃hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w,
    w.length=SquareSampleCompleteVertices.width (IntegralFramedPhysicalBankTerm.input B) c ∧
    ∀i : Fin (IntegralFramedPhysicalSquare.count B.parameters B.plan (B.key c)),
      IntegralFramedPhysicalSquare.joint B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
        B.key B.positive c w hw i=u i.val

private theorem sample_bank (B : IntegralFramedBankQuery.Bank) (c r : List Bool)
    (hr : pairFst (B.key c)=r) (hc : prefixLength B.parameters (B.key c)=(B.plan.rules r).length)
    (u : ℕ→ℝ)
    (hu : (ofCommands (initial B.parameters B.plan r) (B.plan.rules r)
      (by have H := B.plan.room r;omega)).Roots u) : JointSampled B c u :=
  IntegralFramedPhysicalSquare.exists_full_observation B.parameters B.plan B.data
    B.nodes B.factor B.seed B.bounds B.key B.positive c r hr hc u hu

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan

noncomputable def Sampled (old : List Bool) (e : ℕ) (u : ℕ→ℝ) :=
  JointSampled B (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old e)) u

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  JointSampled fullObservation

theorem sample_full_tuple (old : List Bool) (e : ℕ) (u : ℕ→ℝ)
    (hu : (fullObservation old e).Roots u) : Sampled old e u := by
  unfold fullObservation at hu
  unfold Sampled
  have HC : prefixLength (B).parameters ((B).key
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old e)))=
        ((B).plan.rules (preparedRoot old e)).length :=
    (FormulaSignSlotRadialProviderRecordPrefix.full_prefix (preparedRoot old e)).trans
      (full_rules_length (preparedRoot old e)).symm
  exact sample_bank B _ (preparedRoot old e)
    (FormulaSignSlotRadialProviderRecordPrefix.key_root (preparedRoot old e)) HC u hu

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
