/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPlan
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordSeedTail
public import LeanCanny.Encoding.IntegralMixedRoadmapChainSeedTail
/-! # The actual general provider append has a canonical full seed completion -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "oldCs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "x" => FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd e he
local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd e he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he
local notation "hg" => FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd e he
local notation "Q" root => FormulaSignSlotRadialProviderRecordPlan.spatial root
local notation "D" => FormulaSignSlotRadialProviderAtomic.dimension old
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial old

local notation "PLAN" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
variable (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source

noncomputable def meaningfulCodes := IntegralMixedRoadmapChain.meaningfulCodes D
  (payload D old R.leftSpec R.rightSpec side)
noncomputable def tailCount := IntegralMixedRoadmapChain.paddingCount D
  (payload D old R.leftSpec R.rightSpec side)+1
noncomputable def fullBirth := FormulaSignSlotRadialProviderRecordPlan.fullCount r

theorem prepared_seed_records : IntegralMixedCausalRecordPlanBits.records r=WordList.encode
    (meaningfulCodes old hv hd left right R side++
      List.replicate (tailCount old hv hd left right R side)
        (IntegralMixedChronologicalFrameCode.code ((P).ambient r) [] 0 0)) := by
  have H := IntegralMixedRoadmapChain.raw_seed_tail (pair_checked old hv hd left right R side)
    (IntegralMixedRoadmapChain.append_seed_probe D (FormulaSignSlotRadialProviderAtomic.payload old)
      R.leftSpec R.rightSpec side)
  rw [prepared_dimension]
  unfold preparedRoot
  rw [FormulaSignSlotRadialProviderAtomic.root_records,payload_packet]
  simpa only [meaningfulCodes,tailCount,IntegralMixedRoadmapChain.seedCode] using H

theorem meaningful_finish : FormulaSignSlotRadialProviderRecordPlan.count r+
    (meaningfulCodes old hv hd left right R side).length=finishBirth old hv hd left right R side := by
  have HD : IntegralMixedRoadmapChain.depth (payload D old R.leftSpec R.rightSpec side)=
      FormulaSignSlotRadialProviderAtomic.depth old+1 := by
    simp only [payload,IntegralMixedRoadmapChain.append_depth,FormulaSignSlotRadialProviderAtomic.depth]
  rw [meaningfulCodes,IntegralMixedRoadmapChain.meaningfulCodes_length,HD,
    IntegralMixedRoadmapChain.rawStart_succ,pair_start old hv hd left right R side,
    pair_block_count old hv hd left right R side,prepared_initial]
  unfold finishBirth
  rw [begin_eq_start]
  omega

theorem full_birth : fullBirth old hv hd left right R side=
    finishBirth old hv hd left right R side+tailCount old hv hd left right R side := by
  have HC := congrArg WordListRecords.count (prepared_seed_records old hv hd left right R side)
  rw [WordListRecords.count_encode,List.length_append,List.length_replicate] at HC
  change IntegralMixedCausalRecordPlanBits.count r=_ at HC
  have HM := meaningful_finish old hv hd left right R side
  unfold fullBirth FormulaSignSlotRadialProviderRecordPlan.fullCount
  omega

theorem finish_le_full : finishBirth old hv hd left right R side≤fullBirth old hv hd left right R side := by
  rw [full_birth]
  omega

theorem full_rules_length (root : List Bool) :
    ((PLAN).rules root).length=FormulaSignSlotRadialProviderRecordPlan.fullCount root := by
  rw [FormulaSignSlotRadialProviderRecordReceipt.rules,IntegralMixedCausalPlanBits.commands_length,
    FormulaSignSlotRadialProviderRecordReceipt.records_length]
  unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
  omega

theorem full_commands : (PLAN).rules r=
    List.replicate (tailCount old hv hd left right R side)
      (FormulaSignSlotRadialProviderRecordPlan.seedInstruction r)++compiledProgram old hv hd left right R side := by
  have H := FormulaSignSlotRadialProviderRecordPlan.full_seed_tail r []
    (meaningfulCodes old hv hd left right R side) (tailCount old hv hd left right R side)
    (prepared_seed_records old hv hd left right R side)
  rw [meaningful_finish,local_prefix_commands old hv hd left right R side] at H
  exact H

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
