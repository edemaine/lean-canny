/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedProperMetadata
public import LeanCanny.Encoding.IntegralMixedRoadmapProperBase
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalPoint
/-! # Checked proper companion languages from one word's numerical readbacks -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapCheckedCompanionReadback
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "I"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedRoadmapAtomic.root IntegralMixedRoadmapAtomic.context IntegralMixedRoadmapAtomic.word
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalPointCompanionScan.retained
  IntegralMixedPhysicalFieldEquality.point IntegralMixedRoadmapSeedMetadata.stageHeader

variable (q :List Bool)
    (H :IntegralMixedRoadmapChain.Checked (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha q)
      (IntegralMixedRoadmapAtomic.payload q))

noncomputable def midCaptureIndex (hd :0<IntegralMixedRoadmapAtomic.depth q) (i :ℕ)
    (hi :i<IntegralMixedRoadmapProper.captureCount (D q) q) :
    Fin ((B).parameters.ambient (pairFst ((B).key (IntegralMixedRoadmapAtomic.context q)))+1):=
  ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapProper.midFirst (D q) (I q) q+i),
    IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _
      (IntegralMixedRoadmapCheckedProperMetadata.midpoint_capture hn ht ha hR0 q H hd i hi).1⟩

noncomputable def childCaptureIndex (i :ℕ) (hi :i<IntegralMixedRoadmapAtomic.free (D q) q) :
    Fin ((B).parameters.ambient (pairFst ((B).key (IntegralMixedRoadmapAtomic.context q)))+1):=
  ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.first (D q) (I q) q+i),
    IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _
      (IntegralMixedRoadmapCheckedProperMetadata.child_capture hn ht ha hR0 q H i hi).1⟩

include H in
private theorem raw_first_seed :WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) 0=
    IntegralMixedChronologicalFrameCode.code (D q) [] 0 0 :=by
  rw [H.2.2.2.2.2.1]
  simp only [IntegralMixedRoadmapChain.compiled,IntegralMixedRoadmapChain.compiledCodes,
    IntegralMixedRoadmapChain.meaningfulCodes,IntegralMixedRoadmapChain.seedCodes,
    List.cons_append,WordList.get_encode,List.getElem?_cons_zero,Option.getD_some,IntegralMixedRoadmapChain.seedCode]

include H in
private theorem zero_child_anchor (hd :IntegralMixedRoadmapAtomic.depth q=0) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapAtomic.anchor (D q) (I q) q) :=by
  rw [IntegralMixedRoadmapAtomic.seed_anchor _ _ q hd]
  have HCount:=H.2.2.2.2.2.2.1
  have HP :0<WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) :=by
    rw [HCount]
    unfold IntegralMixedRoadmapRecordChain.probedRecordBound
    omega
  have HI :0<IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q) :=by
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [IntegralMixedRoadmapCheckedProperMetadata.root_records]
    exact HP
  have HG :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (IntegralMixedRoadmapAtomic.root q))
      (number n (IntegralMixedRoadmapAtomic.root q)+8) [] 0 0 :=by
    simp [IntegralMixedChronologicalFrameCode.PointGood,IntegralMixedChronologicalFrameCode.Good,WordListRecords.count]
  have HW :IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root q) 0=
      IntegralMixedChronologicalFrameCode.code ((P).ambient (IntegralMixedRoadmapAtomic.root q)) [] 0 0 :=by
    rw [IntegralMixedCausalRecordPlanBits.code,IntegralMixedRoadmapCheckedProperMetadata.root_records,
      IntegralMixedRoadmapCheckedProperMetadata.root_dimension hn ht ha hR0 q]
    exact raw_first_seed hn ht ha hR0 q H
  have HC:=IntegralMixedMarkedRecordReceipt.critical hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q) 0 HI [] 0 0 HG HW
  constructor
  · simpa only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
      pairFst_pair,pairSnd_pair,List.length_replicate,IntegralMixedRoadmapCheckedProperMetadata.full_prefix hn ht ha hR0 q]
      using (show I q<I q+WordListRecords.count
        (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) by omega)
  · rw [IntegralMixedRoadmapCheckedProperMetadata.native_header hn ht ha hR0 q,
      ←IntegralMixedRoadmapCheckedProperMetadata.root_initial hn ht ha hR0 q]
    unfold IntegralMixedRoadmapSeedMetadata.stageHeader
    exact congrArg (fun c=>(IntegralMixedCommandHeaderBits.command c).context) HC

include H in
private theorem child_anchor_active :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapAtomic.anchor (D q) (I q) q) :=by
  by_cases hd :IntegralMixedRoadmapAtomic.depth q=0
  · exact zero_child_anchor hn ht ha hR0 q H hd
  · exact (IntegralMixedRoadmapCheckedProperMetadata.child_anchor hn ht ha hR0 q H (Nat.pos_of_ne_zero hd)).1

include H in
theorem midpoint_of_readback (hd :0<IntegralMixedRoadmapAtomic.depth q)
    (hw :SquareSampleCompleteVertices.Valid S (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q))
    (p :Fin ((B).parameters.ambient (pairFst ((B).key (IntegralMixedRoadmapAtomic.context q)))+1)→ℝ)
    (hAnchor :IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hw
      (IntegralMixedRoadmapProper.midBirth (D q) (I q) q)=p)
    (hPoints :∀i,i<IntegralMixedRoadmapProper.captureCount (D q) q→
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
        (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hw
        (IntegralMixedRoadmapProper.midFirst (D q) (I q) q+i)=p)
    (hFields :∀i (hi :i<IntegralMixedRoadmapProper.captureCount (D q) q),
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hw
        (IntegralMixedRoadmapProper.midFirst (D q) (I q) q+i)=p (midCaptureIndex hn ht ha hR0 q H hd i hi)) :
    IntegralMixedRoadmapProper.Midpoint hn ht ha hR0 q :=by
  let k:=IntegralMixedRoadmapProper.captureCount (D q) q
  have HD :IntegralMixedRoadmapAtomic.depth q≤D q:=H.1
  have HK :0<k:=by unfold k IntegralMixedRoadmapProper.captureCount IntegralMixedRoadmapProper.levelIndex;omega
  have HLast:=(IntegralMixedRoadmapCheckedProperMetadata.midpoint_capture hn ht ha hR0 q H hd (k-1) (by omega)).1
  have HFit :IntegralMixedRoadmapProper.midFirst (D q) (I q) q+k≤
      IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (IntegralMixedRoadmapAtomic.context q)) :=by
    have HB:=(IntegralMixedPhysicalPointCompanionScan.active_direct hn ht ha (radius_binary hR0) false _ _ HLast).1
    dsimp only at HB
    omega
  unfold IntegralMixedRoadmapProper.Midpoint IntegralMixedRoadmapProper.midCompanions IntegralMixedRoadmapAtomic.sampleQuery
  apply (IntegralMixedPhysicalPointCompanionScan.language_packet_iff hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hw _ _ k
    (IntegralMixedRoadmapCheckedProperMetadata.midpoint_anchor hn ht ha hR0 q H hd).1 HFit).mpr
  intro i hi
  have HB:=(IntegralMixedRoadmapCheckedProperMetadata.midpoint_capture hn ht ha hR0 q H hd i hi).1
  refine ⟨HB,(hPoints i hi).trans hAnchor.symm,?_⟩
  rw [hAnchor]
  exact (IntegralMixedPhysicalFieldEquality.retained_point hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hw _ HB).trans (hFields i hi)

include H in
theorem child_of_readback
    (hw :SquareSampleCompleteVertices.Valid S (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q))
    (p :Fin ((B).parameters.ambient (pairFst ((B).key (IntegralMixedRoadmapAtomic.context q)))+1)→ℝ)
    (hAnchor :IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hw
      (IntegralMixedRoadmapAtomic.anchor (D q) (I q) q)=p)
    (hPoints :∀i,i<IntegralMixedRoadmapAtomic.free (D q) q→
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
        (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hw
        (IntegralMixedRoadmapAtomic.first (D q) (I q) q+i)=p)
    (hFields :∀i (hi :i<IntegralMixedRoadmapAtomic.free (D q) q),
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hw
        (IntegralMixedRoadmapAtomic.first (D q) (I q) q+i)=p (childCaptureIndex hn ht ha hR0 q H i hi)) :
    IntegralMixedRoadmapAtomic.companionQuery (D q) (I q) q∈
      IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false :=by
  let k:=IntegralMixedRoadmapAtomic.free (D q) q
  have HD :IntegralMixedRoadmapAtomic.depth q≤D q:=H.1
  have HK :0<k:=by unfold k IntegralMixedRoadmapAtomic.free;omega
  have HLast:=(IntegralMixedRoadmapCheckedProperMetadata.child_capture hn ht ha hR0 q H (k-1) (by omega)).1
  have HFit :IntegralMixedRoadmapAtomic.first (D q) (I q) q+k≤
      IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (IntegralMixedRoadmapAtomic.context q)) :=by
    have HB:=(IntegralMixedPhysicalPointCompanionScan.active_direct hn ht ha (radius_binary hR0) false _ _ HLast).1
    dsimp only at HB
    omega
  unfold IntegralMixedRoadmapAtomic.companionQuery IntegralMixedRoadmapAtomic.sampleQuery
  apply (IntegralMixedPhysicalPointCompanionScan.language_packet_iff hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hw _ _ k
    (child_anchor_active hn ht ha hR0 q H) HFit).mpr
  intro i hi
  have HB:=(IntegralMixedRoadmapCheckedProperMetadata.child_capture hn ht ha hR0 q H i hi).1
  refine ⟨HB,(hPoints i hi).trans hAnchor.symm,?_⟩
  rw [hAnchor]
  exact (IntegralMixedPhysicalFieldEquality.retained_point hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hw _ HB).trans (hFields i hi)

end LeanCanny.Encoding.IntegralMixedRoadmapCheckedCompanionReadback
