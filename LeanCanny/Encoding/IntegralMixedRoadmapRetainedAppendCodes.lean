/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendChild
public import LeanCanny.Encoding.IntegralMixedRoadmapChainSeedTail
/-! # Literal midpoint and child bytes of the retained-endpoint append -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedPointCompanion IntegralMixedChronologicalFrame IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem append_raw_middle (n :ℕ) (q :List Bool)
    (l r :List Bool) (side :Bool) (p :List Bool) (i :ℕ)
    (hi :i<(IntegralMixedRoadmapLevel.codes n
      (IntegralMixedRoadmapLevel.packet (IntegralMixedRoadmapChain.frozen q
        (IntegralMixedRoadmapChain.depth q)) l r side [])).length):
    WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapChain.appendPayload n q l r side p))
      (IntegralMixedRoadmapChain.rawStart n q (IntegralMixedRoadmapChain.depth q)+i)=
      ((IntegralMixedRoadmapLevel.codes n (IntegralMixedRoadmapLevel.packet
        (IntegralMixedRoadmapChain.frozen q (IntegralMixedRoadmapChain.depth q)) l r side []))[i]?).getD []:=by
  let q' :=IntegralMixedRoadmapChain.appendPayload n q l r side p
  have HD :IntegralMixedRoadmapChain.depth q'=IntegralMixedRoadmapChain.depth q+1:=
    IntegralMixedRoadmapChain.append_depth n q l r side p
  obtain ⟨before,after,HE,HL⟩:=IntegralMixedRoadmapChain.compiledCodes_split n q'
    (IntegralMixedRoadmapChain.depth q) (by omega)
  have HT:=IntegralMixedRoadmapChain.append_template_last n q l r side p
  have HS:=IntegralMixedRoadmapChain.append_rawStart_before n q l r side p
    (IntegralMixedRoadmapChain.depth q) le_rfl
  rw [HT] at HE
  rw [HS] at HL
  have HR :IntegralMixedRoadmapChain.raw q'=IntegralMixedRoadmapChain.compiled n q':=
    IntegralMixedRoadmapChain.completePayload_raw n _ p
  change WordList.get (IntegralMixedRoadmapChain.raw q') _=_
  rw [HR,IntegralMixedRoadmapChain.compiled,HE,←HL,WordList.get_encode,List.append_assoc,
    List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,List.getElem?_append_left hi]

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "Q" r=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (e :ℕ) (he :e<IntegralMixedRoadmapAtomic.endBirth
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)
local notation "r"=>preparedRoot hn ht ha hR0 old e
local notation "d"=>parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "a"=>endpointLabel hn ht ha hR0 old hv hd e he
local notation "F"=>IntegralMixedChronologicalMidpoint.frame d hk a a
local notation "g"=>midpointObjective hn ht ha hR0 old hv hd e he
local notation "js"=>midpointSelections hn ht ha hR0 old hv hd e he
local notation "dc"=>childDescriptor hn ht ha hR0 old hv hd e he
local notation "gc"=>childObjective hn ht ha hR0 old hv hd e he
local notation "cs"=>childSelections hn ht ha hR0 old hv hd e he

noncomputable def midpointCodes:=IntegralMixedPointCompanion.codes (F).frozen
  (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
  (IntegralMixedChronologicalMidpoint.rows d hk a a) g js
noncomputable def childCodes:=IntegralMixedPointCompanion.codes (dc).frame.frozen
  (fun _=>false) (fun i=>.single ((dc).atom i)) gc cs
noncomputable def localCodes:=childCodes hn ht ha hR0 old hv hd e he++midpointCodes hn ht ha hR0 old hv hd e he

theorem child_labels_literal :IntegralMixedChronologicalFrameCode.labels dc=
    IntegralMixedChronologicalEndpointCode.appendLabels (IntegralMixedRoadmapAtomic.frozen old) e:=by
  rw [childDescriptor,IntegralMixedChronologicalEndpoint.retainMany_labels,
    ←IntegralMixedChronologicalEndpointCode.append_actual,parent_labels]
  rfl

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap preparedRoot parentCommands parentDescriptor
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedRoadmapAtomic.depth IntegralMixedRoadmapAtomic.frozen
  IntegralMixedChronologicalFrameCode.code IntegralMixedChronologicalMidpointCode.code

theorem local_codes_compiled :(localCodes hn ht ha hR0 old hv hd e he).reverse=
    IntegralMixedRoadmapLevel.codes ((P).ambient r)
      (IntegralMixedRoadmapLevel.packet (IntegralMixedRoadmapAtomic.frozen old) (endpoint e) (endpoint e) false []):=by
  have HM:=midpoint_block_codes d hk a a g
  have HC:=atomic_block_codes dc gc
  have HG :(g).val.val=IntegralMixedRoadmapAtomic.depth old+1:=by
    change (d).labels.length+1=_
    rw [parent_descriptor_length]
  have HGC :(gc).val.val=IntegralMixedRoadmapAtomic.depth old+1:=HG
  have HA :(a).val=e:=rfl
  simp only [parent_labels,HA,HG] at HM
  simp only [child_labels_literal,HGC] at HC
  rw [localCodes,List.reverse_append]
  change (midpointCodes hn ht ha hR0 old hv hd e he).reverse++
    (childCodes hn ht ha hR0 old hv hd e he).reverse=_
  rw [show (midpointCodes hn ht ha hR0 old hv hd e he).reverse=_ from HM,
    show (childCodes hn ht ha hR0 old hv hd e he).reverse=_ from HC]
  simp only [IntegralMixedRoadmapLevel.codes,IntegralMixedRoadmapLevel.midpointAnchor,
    IntegralMixedRoadmapLevel.childAnchor,IntegralMixedRoadmapLevel.childLabels,
    IntegralMixedRoadmapLevel.chosen,IntegralMixedRoadmapLevel.producer,IntegralMixedRoadmapLevel.g,
    IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.left,
    IntegralMixedRoadmapLevel.right,IntegralMixedRoadmapLevel.sideWord,IntegralMixedRoadmapLevel.packet,
    pairFst_pair,pairSnd_pair,IntegralMixedRoadmapEndpointSyntax.codes,endpoint,
    IntegralMixedRoadmapEndpointSyntax.field_spec_0,IntegralMixedRoadmapEndpointSyntax.field_spec_1,
    ite_true,IntegralMixedRoadmapAtomic.frozen_count,List.nil_append,List.append_assoc,reduceCtorEq,ite_false]
  rfl

theorem local_codes_length :(localCodes hn ht ha hR0 old hv hd e he).length=
    2+2*(IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old-IntegralMixedRoadmapAtomic.depth old):=by
  simp only [localCodes,childCodes,midpointCodes,List.length_append,IntegralMixedPointCompanion.codes_length,
    child_selection_count,midpoint_selection_count]
  omega

attribute [local irreducible] midpointObjective childDescriptor childObjective
  midpointCodes childCodes localCodes IntegralMixedRoadmapAtomic.root IntegralMixedRoadmapAtomic.payload
  IntegralMixedCausalRecordPlanBits.code IntegralMixedCausalRecordPlanBits.records
  IntegralMixedRoadmapChain.raw IntegralMixedRoadmapChain.template IntegralMixedRoadmapChain.compiledCodes
  IntegralMixedRoadmapLevel.codes

theorem local_code_at (i :ℕ) (hi :i<(localCodes hn ht ha hR0 old hv hd e he).length):
    IntegralMixedCausalRecordPlanBits.code r (start hn ht ha hR0 old+i)=
      ((localCodes hn ht ha hR0 old hv hd e he).reverse[i]?).getD []:=by
  have HL:=local_codes_compiled hn ht ha hR0 old hv hd e he
  rw [prepared_dimension] at HL
  have HI :i<(IntegralMixedRoadmapLevel.codes (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
      (IntegralMixedRoadmapLevel.packet (IntegralMixedRoadmapAtomic.frozen old) (endpoint e) (endpoint e) false [])).length:=by
    rw [←HL,List.length_reverse]
    exact hi
  have HR:=append_raw_middle (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (IntegralMixedRoadmapAtomic.payload old) (endpoint e) (endpoint e) false
    (IntegralMixedRoadmapChain.seedCode (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)) i
    (by simpa only [IntegralMixedRoadmapAtomic.frozen,IntegralMixedRoadmapAtomic.depth] using HI)
  have HF :IntegralMixedRoadmapChain.frozen (IntegralMixedRoadmapAtomic.payload old)
      (IntegralMixedRoadmapChain.depth (IntegralMixedRoadmapAtomic.payload old))=
        IntegralMixedRoadmapAtomic.frozen old:=by
    simp only [IntegralMixedRoadmapAtomic.frozen,IntegralMixedRoadmapAtomic.depth]
  rw [HF] at HR
  rw [←HL] at HR
  simpa only [IntegralMixedCausalRecordPlanBits.code,IntegralMixedCausalRecordPlanBits.records,
    preparedRoot,IntegralMixedRoadmapAtomic.root,payload_packet,pairFst_pair,pairSnd_pair,payload,
    start,IntegralMixedRoadmapAtomic.depth] using HR

noncomputable def retainedCodes:=IntegralMixedRoadmapChain.meaningfulCodes
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old e)
noncomputable def seedTailCount:=IntegralMixedRoadmapChain.paddingCount
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old e)+1

include hv hd he in
theorem prepared_records_tail :IntegralMixedCausalRecordPlanBits.records r=WordList.encode
    (retainedCodes hn ht ha hR0 old e++List.replicate (seedTailCount hn ht ha hR0 old e)
      (IntegralMixedChronologicalFrameCode.code ((P).ambient r) [] 0 0)):=by
  have HC:=checked hn ht ha hR0 old hv hd e he []
  have HP :IntegralMixedRoadmapChain.probe
      (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old e)=
        IntegralMixedRoadmapChain.seedCode (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old):=by
    unfold payload
    exact IntegralMixedRoadmapChain.append_seed_probe _ _ _ _ _
  have HT:=IntegralMixedRoadmapChain.raw_seed_tail HC HP
  rw [prepared_dimension]
  simpa only [IntegralMixedCausalRecordPlanBits.records,preparedRoot,IntegralMixedRoadmapAtomic.root,
    payload_packet,pairFst_pair,pairSnd_pair,retainedCodes,seedTailCount,IntegralMixedRoadmapChain.seedCode] using HT

theorem retained_codes_birth :IntegralMixedAuxiliaryMarkedIntegerSource.number n r+8+
    (retainedCodes hn ht ha hR0 old e).length=finishBirth hn ht ha hR0 old e:=by
  rw [retainedCodes,IntegralMixedRoadmapChain.meaningfulCodes_length]
  change _=IntegralMixedRoadmapAtomic.endBirth _ _ _
  rw [IntegralMixedRoadmapAtomic.endBirth,payload_packet,depth_packet,initial_root]
  simp only [payload,IntegralMixedRoadmapChain.append_depth,IntegralMixedRoadmapAtomic.depth]

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
