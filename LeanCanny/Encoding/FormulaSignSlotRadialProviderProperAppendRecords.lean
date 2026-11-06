/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendCodes
/-! # The actual provider record bytes are the complete constructed proper level -/
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
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "x" => FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd e he
local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd e he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he
local notation "hg" => FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd e he
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial c
local notation "D" => FormulaSignSlotRadialProviderAtomic.dimension old
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial old

private theorem end_birth_expand (n baseCount : ℕ) (q : List Bool) :
    FormulaSignSlotRadialProviderAtomic.endBirth n baseCount q=
      baseCount+IntegralMixedRoadmapChain.rawStart n (FormulaSignSlotRadialProviderAtomic.payload q)
        (FormulaSignSlotRadialProviderAtomic.depth q) := rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth FormulaSignSlotRadialProviderAtomic.payload
  FormulaSignSlotRadialProviderAtomic.frozen FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands
variable (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right)

theorem pair_template (side :Bool):
    IntegralMixedRoadmapChain.template (payload D old R.leftSpec R.rightSpec side)
      (FormulaSignSlotRadialProviderAtomic.depth old)=IntegralMixedRoadmapLevel.packet
        (FormulaSignSlotRadialProviderAtomic.frozen old) R.leftSpec R.rightSpec side []:=by
  simpa only [payload,FormulaSignSlotRadialProviderAtomic.frozen,FormulaSignSlotRadialProviderAtomic.depth] using
    IntegralMixedRoadmapChain.append_template_last D (FormulaSignSlotRadialProviderAtomic.payload old)
      R.leftSpec R.rightSpec side (IntegralMixedRoadmapChain.seedCode D)

theorem pair_start (side :Bool):
    IntegralMixedRoadmapChain.rawStart D (payload D old R.leftSpec R.rightSpec side)
      (FormulaSignSlotRadialProviderAtomic.depth old)=start old:=by
  simpa only [payload,start,FormulaSignSlotRadialProviderAtomic.depth] using
    IntegralMixedRoadmapChain.append_rawStart_before D (FormulaSignSlotRadialProviderAtomic.payload old)
      R.leftSpec R.rightSpec side (IntegralMixedRoadmapChain.seedCode D)
      (IntegralMixedRoadmapChain.depth (FormulaSignSlotRadialProviderAtomic.payload old)) le_rfl

theorem pair_block_count (side :Bool):
    IntegralMixedRoadmapChain.blockCount D (payload D old R.leftSpec R.rightSpec side)
      (FormulaSignSlotRadialProviderAtomic.depth old)=(R.levelCodes hk g hg side).length:=by
  have HT:=IntegralMixedRoadmapChain.template_codes_length D
    (payload D old R.leftSpec R.rightSpec side) (FormulaSignSlotRadialProviderAtomic.depth old)
  rw [pair_template old hv hd left right R side] at HT
  have HL:=congrArg List.length (level_codes_compiled old hv hd left right R side)
  rw [List.length_reverse] at HL
  exact HT.symm.trans HL.symm

theorem level_word_compiled (side :Bool):
    WordList.encode (R.levelCodes hk g hg side).reverse=IntegralMixedRoadmapLevel.compiled D
      (IntegralMixedRoadmapLevel.packet (FormulaSignSlotRadialProviderAtomic.frozen old) R.leftSpec R.rightSpec side []):=
  congrArg WordList.encode (level_codes_compiled old hv hd left right R side)

theorem level_slice (side :Bool):
    IntegralMixedRoadmapLevel.rawSlice (IntegralMixedRoadmapChain.raw
      (payload D old R.leftSpec R.rightSpec side)) (start old)
      (R.levelCodes hk g hg side).length=WordList.encode (R.levelCodes hk g hg side).reverse:=by
  have HC:=pair_checked old hv hd left right R side
  have HD :IntegralMixedRoadmapChain.depth (payload D old R.leftSpec R.rightSpec side)=
      FormulaSignSlotRadialProviderAtomic.depth old+1:=by
    simp only [payload,IntegralMixedRoadmapChain.append_depth,FormulaSignSlotRadialProviderAtomic.depth]
  have HS:=IntegralMixedRoadmapChain.compiled_level_slice D
    (payload D old R.leftSpec R.rightSpec side) (FormulaSignSlotRadialProviderAtomic.depth old) (by omega)
  rw [←HC.2.2.2.2.2.1,pair_start old hv hd left right R side,
    pair_block_count old hv hd left right R side,
    pair_template old hv hd left right R side] at HS
  exact HS.trans (level_word_compiled old hv hd left right R side).symm

theorem local_code_fit (side :Bool):
    start old+(R.levelCodes hk g hg side).length≤
      IntegralMixedCausalRecordPlanBits.count (preparedRoot old R.leftSpec R.rightSpec side):=by
  have HC:=pair_checked old hv hd left right R side
  have HD :IntegralMixedRoadmapChain.depth (payload D old R.leftSpec R.rightSpec side)=
      FormulaSignSlotRadialProviderAtomic.depth old+1:=by
    simp only [payload,IntegralMixedRoadmapChain.append_depth,FormulaSignSlotRadialProviderAtomic.depth]
  have HF:=IntegralMixedRoadmapChain.compiled_level_fits D
    (payload D old R.leftSpec R.rightSpec side) (FormulaSignSlotRadialProviderAtomic.depth old) (by omega)
  rw [←HC.2.2.2.2.2.1,pair_start old hv hd left right R side,
    pair_block_count old hv hd left right R side] at HF
  unfold IntegralMixedCausalRecordPlanBits.count preparedRoot
  rw [FormulaSignSlotRadialProviderAtomic.root_records,payload_packet]
  exact HF

theorem local_code_at (side :Bool) (i :ℕ) (hi :i<(R.levelCodes hk g hg side).length):
    IntegralMixedCausalRecordPlanBits.code
      (preparedRoot old R.leftSpec R.rightSpec side) (start old+i)=
        ((R.levelCodes hk g hg side).reverse[i]?).getD []:=by
  have HS:=congrArg (fun w=>WordList.get w i) (level_slice old hv hd left right R side)
  simp only [IntegralMixedRoadmapLevel.rawSlice,WordList.get_encode,List.getElem?_map,
    List.getElem?_range hi,Option.map_some,Option.getD_some] at HS
  unfold preparedRoot
  rw [FormulaSignSlotRadialProviderAtomic.root_record_code,payload_packet]
  exact HS


theorem end_birth (side :Bool) (w :List Bool):
    FormulaSignSlotRadialProviderAtomic.endBirth
      (FormulaSignSlotRadialProviderAtomic.dimension (packet D old R.leftSpec R.rightSpec side w))
      (FormulaSignSlotRadialProviderAtomic.initial (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=
        beginBirth old+(R.levelCodes hk g hg side).length:=by
  rw [dimension_packet,initial_packet,end_birth_expand,payload_packet,depth_packet,
    IntegralMixedRoadmapChain.rawStart_succ,pair_start old hv hd left right R side,
    pair_block_count old hv hd left right R side]
  have HB :N+start old=beginBirth old:=(begin_eq_start old).symm
  omega

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
