/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPrefix
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCanonicalEndpoints
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelRecord
/-! # A canonical realized endpoint pair compiles the actual appended level -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "cs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "z"=>IntegralMixedRoadmapRetainedAppend.parentTuple hn ht ha hR0 old hv hd e he
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd e he
local notation "Q"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c
local notation "cap"=>IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old

noncomputable local instance :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs

noncomputable abbrev ParentEndpoint:=Endpoint (cs).length
noncomputable abbrev CanonicalPair (left right :ParentEndpoint hn ht ha hR0 old hv hd):=
  NativePair x d z (IntegralMixedRoadmapProperParent.hom hn ht ha hR0 old hv hd) V left right
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha c) cap

private theorem canonical_width :(P).width c=IntegralMixedRoadmapAtomic.width hn ht ha hR0 old:=by
  have H:=IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 c (IntegralMixedRoadmapAtomic.root old)
    (IntegralMixedRoadmapRetainedAppend.prepared_candidate hn ht ha hR0 old e)
  exact H

private theorem canonical_source_cap :IntegralMixedExceptionalBounds.auxiliaryCap ((P).ambient c+1) (Q).degree=
    IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 old:=by
  rw [IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree,
    IntegralMixedRoadmapRetainedAppend.prepared_dimension]
  have H:=IntegralMixedMarkedPrefixParameters.degree hn ht ha hR0 c (IntegralMixedRoadmapAtomic.root old)
    (IntegralMixedRoadmapRetainedAppend.prepared_candidate hn ht ha hR0 old e)
  change IntegralMixedExceptionalBounds.auxiliaryCap (D+1) ((P).degree c)=_
  rw [H]
  rfl

private theorem canonical_birth :(cs).length=beginBirth hn ht ha hR0 old:=
  IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 old hv hd e he

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.width IntegralMixedRoadmapAtomic.sourceCap
  IntegralMixedRoadmapAtomic.depth IntegralMixedRoadmapAtomic.frozen IntegralMixedRoadmapAtomic.payload
  IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentState IntegralMixedRoadmapRetainedAppend.parentDescriptor
  IntegralMixedRoadmapRetainedAppend.parentTuple IntegralMixedRoadmapRetainedAppend.parentValues
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedFramedRawHeight.rootCeiling
  IntegralMixedFramedNormalizationBits.requiredModulus

variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right)

private theorem endpoint_good_transport {n1 n2 B1 B2 C1 C2 m1 m2 u1 u2 :ℕ}
    {labels labels' w :List Bool}
    (H :IntegralMixedRoadmapEndpointSyntax.Good n1 B1 C1 m1 u1 labels w)
    (hn :n1=n2) (hB :B1=B2) (hC :C1=C2) (hm :m1=m2) (hu :u1=u2) (hl :labels=labels'):
    IntegralMixedRoadmapEndpointSyntax.Good n2 B2 C2 m2 u2 labels' w:=by
  cases hn
  cases hB
  cases hC
  cases hm
  cases hu
  cases hl
  exact H

theorem endpoints_good :EndpointsGood hn ht ha hR0 old R.leftSpec R.rightSpec:=by
  have HBounds :(d).labels.length+1<(P).ambient c+1:=by
    rw [IntegralMixedRoadmapRetainedAppend.parent_descriptor_length,
      IntegralMixedRoadmapRetainedAppend.prepared_dimension]
    omega
  have H:=(R.levelRecord_checked false HBounds).1
  have HL:=H.2.2.1
  have HR:=H.2.2.2.1
  simp only [NativePair.levelRecord,IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.left,
    IntegralMixedRoadmapLevel.right,IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.packet,
    pairFst_pair,pairSnd_pair] at HL HR
  have HN:=IntegralMixedRoadmapRetainedAppend.prepared_dimension hn ht ha hR0 old e
  have HB:=canonical_width hn ht ha hR0 old
  have HC:=canonical_source_cap hn ht ha hR0 old
  have HM:=canonical_birth hn ht ha hR0 old hv hd
  have HLabels:=IntegralMixedRoadmapRetainedAppend.parent_labels hn ht ha hR0 old hv hd e he
  exact ⟨endpoint_good_transport HL HN HB HC HM HM HLabels,
    endpoint_good_transport HR HN HB HC HM
      (congrArg (fun m=>m+IntegralMixedRoadmapEndpointSyntax.fresh R.leftSpec) HM) HLabels⟩

theorem pair_checked (side :Bool) (w :List Bool):
    IntegralMixedRoadmapChain.Checked D
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      N (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha old)
      (payload D old R.leftSpec R.rightSpec side):=
  checked hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side
    (endpoints_good hn ht ha hR0 old hv hd left right R) w

theorem level_codes_compiled (side :Bool):
    (R.levelCodes hk g hg side).reverse=IntegralMixedRoadmapLevel.codes D
      (IntegralMixedRoadmapLevel.packet (IntegralMixedRoadmapAtomic.frozen old) R.leftSpec R.rightSpec side []):=by
  have H:=R.levelCodes_compiled hk g hg
    (IntegralMixedRoadmapProperParent.objective_value hn ht ha hR0 old hv hd) side
  refine H.trans ?_
  apply congrArg₂ IntegralMixedRoadmapLevel.codes
  · exact IntegralMixedRoadmapRetainedAppend.prepared_dimension hn ht ha hR0 old e
  · simp only [NativePair.levelPacket,IntegralMixedRoadmapRetainedAppend.parent_labels]

theorem level_code_count (side :Bool):
    (R.levelCodes hk g hg side).length=IntegralMixedRoadmapEndpointSyntax.fresh R.leftSpec+
      IntegralMixedRoadmapEndpointSyntax.fresh R.rightSpec+2+2*(D-IntegralMixedRoadmapAtomic.depth old):=by
  have H:=congrArg List.length (level_codes_compiled hn ht ha hR0 old hv hd left right R side)
  simp only [List.length_reverse,IntegralMixedRoadmapLevel.codes_length,IntegralMixedRoadmapLevel.freshLeft,
    IntegralMixedRoadmapLevel.freshRight,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.freeCount,IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapLevel.k,
    IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair,
    IntegralMixedRoadmapAtomic.frozen_count] at H
  omega

theorem pair_template (side :Bool):
    IntegralMixedRoadmapChain.template (payload D old R.leftSpec R.rightSpec side)
      (IntegralMixedRoadmapAtomic.depth old)=IntegralMixedRoadmapLevel.packet
        (IntegralMixedRoadmapAtomic.frozen old) R.leftSpec R.rightSpec side []:=by
  simpa only [payload,IntegralMixedRoadmapAtomic.frozen,IntegralMixedRoadmapAtomic.depth] using
    IntegralMixedRoadmapChain.append_template_last D (IntegralMixedRoadmapAtomic.payload old)
      R.leftSpec R.rightSpec side (IntegralMixedRoadmapChain.seedCode D)

theorem pair_start (side :Bool):
    IntegralMixedRoadmapChain.rawStart D (payload D old R.leftSpec R.rightSpec side)
      (IntegralMixedRoadmapAtomic.depth old)=start hn ht ha hR0 old:=by
  simpa only [payload,start,IntegralMixedRoadmapAtomic.depth] using
    IntegralMixedRoadmapChain.append_rawStart_before D (IntegralMixedRoadmapAtomic.payload old)
      R.leftSpec R.rightSpec side (IntegralMixedRoadmapChain.seedCode D)
      (IntegralMixedRoadmapChain.depth (IntegralMixedRoadmapAtomic.payload old)) le_rfl

theorem pair_block_count (side :Bool):
    IntegralMixedRoadmapChain.blockCount D (payload D old R.leftSpec R.rightSpec side)
      (IntegralMixedRoadmapAtomic.depth old)=(R.levelCodes hk g hg side).length:=by
  have HT:=IntegralMixedRoadmapChain.template_codes_length D
    (payload D old R.leftSpec R.rightSpec side) (IntegralMixedRoadmapAtomic.depth old)
  rw [pair_template hn ht ha hR0 old hv hd left right R side] at HT
  have HL:=congrArg List.length (level_codes_compiled hn ht ha hR0 old hv hd left right R side)
  rw [List.length_reverse] at HL
  exact HT.symm.trans HL.symm

theorem level_word_compiled (side :Bool):
    WordList.encode (R.levelCodes hk g hg side).reverse=IntegralMixedRoadmapLevel.compiled D
      (IntegralMixedRoadmapLevel.packet (IntegralMixedRoadmapAtomic.frozen old) R.leftSpec R.rightSpec side []):=
  congrArg WordList.encode (level_codes_compiled hn ht ha hR0 old hv hd left right R side)

theorem level_slice (side :Bool):
    IntegralMixedRoadmapLevel.rawSlice (IntegralMixedRoadmapChain.raw
      (payload D old R.leftSpec R.rightSpec side)) (start hn ht ha hR0 old)
      (R.levelCodes hk g hg side).length=WordList.encode (R.levelCodes hk g hg side).reverse:=by
  have HC:=pair_checked hn ht ha hR0 old hv hd left right R side []
  have HD :IntegralMixedRoadmapChain.depth (payload D old R.leftSpec R.rightSpec side)=
      IntegralMixedRoadmapAtomic.depth old+1:=by
    simp only [payload,IntegralMixedRoadmapChain.append_depth,IntegralMixedRoadmapAtomic.depth]
  have HS:=IntegralMixedRoadmapChain.compiled_level_slice D
    (payload D old R.leftSpec R.rightSpec side) (IntegralMixedRoadmapAtomic.depth old) (by omega)
  rw [←HC.2.2.2.2.2.1,pair_start hn ht ha hR0 old hv hd left right R side,
    pair_block_count hn ht ha hR0 old hv hd left right R side,
    pair_template hn ht ha hR0 old hv hd left right R side] at HS
  exact HS.trans (level_word_compiled hn ht ha hR0 old hv hd left right R side).symm

theorem local_code_fit (side :Bool):
    start hn ht ha hR0 old+(R.levelCodes hk g hg side).length≤
      IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side):=by
  have HC:=pair_checked hn ht ha hR0 old hv hd left right R side []
  have HD :IntegralMixedRoadmapChain.depth (payload D old R.leftSpec R.rightSpec side)=
      IntegralMixedRoadmapAtomic.depth old+1:=by
    simp only [payload,IntegralMixedRoadmapChain.append_depth,IntegralMixedRoadmapAtomic.depth]
  have HF:=IntegralMixedRoadmapChain.compiled_level_fits D
    (payload D old R.leftSpec R.rightSpec side) (IntegralMixedRoadmapAtomic.depth old) (by omega)
  rw [←HC.2.2.2.2.2.1,pair_start hn ht ha hR0 old hv hd left right R side,
    pair_block_count hn ht ha hR0 old hv hd left right R side] at HF
  simpa only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    preparedRoot,IntegralMixedRoadmapAtomic.root,payload_packet,pairFst_pair,pairSnd_pair] using HF

theorem local_code_at (side :Bool) (i :ℕ) (hi :i<(R.levelCodes hk g hg side).length):
    IntegralMixedCausalRecordPlanBits.code
      (preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side) (start hn ht ha hR0 old+i)=
        ((R.levelCodes hk g hg side).reverse[i]?).getD []:=by
  have HS:=congrArg (fun w=>WordList.get w i) (level_slice hn ht ha hR0 old hv hd left right R side)
  simp only [IntegralMixedRoadmapLevel.rawSlice,WordList.get_encode,List.getElem?_map,
    List.getElem?_range hi,Option.map_some,Option.getD_some] at HS
  simpa only [IntegralMixedCausalRecordPlanBits.code,IntegralMixedCausalRecordPlanBits.records,
    preparedRoot,IntegralMixedRoadmapAtomic.root,payload_packet,pairFst_pair,pairSnd_pair] using HS

theorem end_birth (side :Bool) (w :List Bool):
    IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=
        beginBirth hn ht ha hR0 old+(R.levelCodes hk g hg side).length:=by
  rw [dimension_packet,initial_packet,IntegralMixedRoadmapAtomic.endBirth,payload_packet,depth_packet,
    IntegralMixedRoadmapChain.rawStart_succ,pair_start hn ht ha hR0 old hv hd left right R side,
    pair_block_count hn ht ha hR0 old hv hd left right R side]
  have HB :N+start hn ht ha hR0 old=beginBirth hn ht ha hR0 old:=rfl
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
