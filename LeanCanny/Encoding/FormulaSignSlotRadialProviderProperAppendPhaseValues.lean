/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendScalarReadback
/-! # Exact scalar anchors and captures for distinct actual proper-level points -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedChronologicalLevelScalarValues
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  canonicalObservation compiledProgram fullObservation
variable {old : List Bool} {hv : FormulaSignSlotRadialProviderAtomic.Valid old}
  {hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he

theorem SampledLevel.local_values_count (_S : SampledLevel old hv hd left right R side pMID pChild) :
    (cs).length+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length=
      finishBirth old hv hd left right R side := by
  have HL : (cs).length=beginBirth old := FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd e he
  unfold finishBirth
  rw [R.levelCodes_length]
  omega

theorem SampledLevel.local_value_at (S : SampledLevel old hv hd left right R side pMID pChild)
    (i : Fin ((cs).length+R.result.commands.length+1+
      (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length+1+
      (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length)) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid
      (finishBirth old hv hd left right R side-1-i.val)=levelValues pMID pChild R.result.nextValues
        (FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he) (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)) i := by
  have HI := i.isLt.trans_eq S.local_values_count
  have H := S.receipt.local_field (finishBirth old hv hd left right R side-1-i.val) (by omega)
  have HE : finishBirth old hv hd left right R side-1-(finishBirth old hv hd left right R side-1-i.val)=i.val := by omega
  exact H.trans ((congrArg (fun k=>(canonicalObservation old hv hd left right R side).point S.localTuple k) HE).trans
    (S.local_values i))

theorem SampledLevel.child_anchor_field (S : SampledLevel old hv hd left right R side pMID pChild) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid
      (((cs).length+R.result.commands.length)+1+(R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length)=
      pChild (FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he) := by
  have HF := S.local_values_count
  have H := S.local_value_at ⟨(R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length,by omega⟩
  have HV := IntegralMixedChronologicalLevelScalarValues.child_anchor pMID pChild R.result.nextValues (FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he)
    (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he))
  have HE : finishBirth old hv hd left right R side-1-(R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length=
      ((cs).length+R.result.commands.length)+1+(R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length := by omega
  exact (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid b) HE).symm.trans
    (H.trans HV)

theorem SampledLevel.midpoint_anchor_field (S : SampledLevel old hv hd left right R side pMID pChild) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid
      ((cs).length+R.result.commands.length)=pMID (FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he) := by
  have HF := S.local_values_count
  have H := S.local_value_at ⟨(R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length+1+
    (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length,by omega⟩
  have HV := IntegralMixedChronologicalLevelScalarValues.midpoint_anchor pMID pChild R.result.nextValues (FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he)
    (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he))
  have HE : finishBirth old hv hd left right R side-1-((R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length+1+
      (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length)=((cs).length+R.result.commands.length) := by omega
  exact (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid b) HE).symm.trans
    (H.trans HV)

theorem SampledLevel.child_capture_field (S : SampledLevel old hv hd left right R side pMID pChild)
    (k : Fin (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid
      (((cs).length+R.result.commands.length)+2+(R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length+
        ((R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length-1-k.val))=
      pChild ((R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).get k).val := by
  have HF := S.local_values_count
  have HK := k.isLt
  have H := S.local_value_at ⟨k.val,by omega⟩
  have HV := IntegralMixedChronologicalLevelScalarValues.child_capture pMID pChild R.result.nextValues (FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he)
    (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)) k
  have HE : finishBirth old hv hd left right R side-1-k.val=((cs).length+R.result.commands.length)+2+
      (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length+
        ((R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length-1-k.val) := by omega
  exact (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid b) HE).symm.trans
    (H.trans HV)

theorem SampledLevel.midpoint_capture_field (S : SampledLevel old hv hd left right R side pMID pChild)
    (k : Fin (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid
      (((cs).length+R.result.commands.length)+1+
        ((R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length-1-k.val))=
      pMID ((R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).get k).val := by
  have HF := S.local_values_count
  have HK := k.isLt
  have H := S.local_value_at ⟨(R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length+1+k.val,by omega⟩
  have HV := IntegralMixedChronologicalLevelScalarValues.midpoint_capture pMID pChild R.result.nextValues (FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he)
    (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)) k
  have HE : finishBirth old hv hd left right R side-1-((R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length+1+k.val)=
      ((cs).length+R.result.commands.length)+1+
        ((R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length-1-k.val) := by omega
  exact (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid b) HE).symm.trans
    (H.trans HV)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
