/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendMidpointHeader
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendChildHeader
public import LeanCanny.Encoding.IntegralMixedRoadmapChainSeedTail
public import LeanCanny.Encoding.IntegralFramedCreatingCut
/-! # Every new stage of a retained-endpoint extension is genuinely critical -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem raw_seed_get {d B sourceCap initial C : ℕ} {q : List Bool}
    (hc : IntegralMixedRoadmapChain.Checked d B sourceCap initial C q)
    (hp : IntegralMixedRoadmapChain.probe q=IntegralMixedRoadmapChain.seedCode d)
    (i : ℕ) (hi : IntegralMixedRoadmapChain.rawStart d q (IntegralMixedRoadmapChain.depth q) ≤ i)
    (hj : i < WordListRecords.count (IntegralMixedRoadmapChain.raw q)) :
    WordList.get (IntegralMixedRoadmapChain.raw q) i=IntegralMixedRoadmapChain.seedCode d :=by
  have HR:=IntegralMixedRoadmapChain.raw_seed_tail hc hp
  have HL:=IntegralMixedRoadmapChain.meaningfulCodes_length d q
  have HB : i-(IntegralMixedRoadmapChain.meaningfulCodes d q).length<
      IntegralMixedRoadmapChain.paddingCount d q+1:=by
    rw [HR,WordListRecords.count_encode,List.length_append,List.length_replicate] at hj
    omega
  rw [HR,WordList.get_encode,List.getElem?_append_right (by omega)]
  simp only [List.getElem?_replicate,HB,ite_true,Option.getD_some]

private theorem empty_point_good (d b : ℕ) : IntegralMixedChronologicalFrameCode.PointGood d b [] 0 0 :=by
  simp [IntegralMixedChronologicalFrameCode.PointGood,IntegralMixedChronologicalFrameCode.Good,
    WordListRecords.count]

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "PLAN"=>IntegralFramedBankQuery.Bank.plan B
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "ROOT"=>preparedRoot hn ht ha hR0
local notation "CTX"=>context hn ht ha hR0
local notation "Q"=>(fun old e=>packet (D old) old e [])
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  preparedRoot context beginBirth finishBirth fullBirth IntegralMixedRoadmapSeedMetadata.stageHeader

theorem seed_code_after_finish (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (b : ℕ)
    (hb0 : finishBirth hn ht ha hR0 old e≤b) (hb1 : b<fullBirth hn ht ha hR0 old e) :
    IntegralMixedCausalRecordPlanBits.code (ROOT old e) (b-N old)=IntegralMixedRoadmapChain.seedCode (D old) :=by
  let q:=Q old e
  have HC:=midpoint_checked hn ht ha hR0 old hv hd e he []
  have HP : IntegralMixedRoadmapChain.probe (IntegralMixedRoadmapAtomic.payload q)=IntegralMixedRoadmapChain.seedCode (D old):=by
    simpa only [q,payload_packet,payload] using IntegralMixedRoadmapChain.append_seed_probe (D old)
      (IntegralMixedRoadmapAtomic.payload old) (endpoint e) (endpoint e) false
  have HF : finishBirth hn ht ha hR0 old e=N old+
      IntegralMixedRoadmapChain.rawStart (D old) (IntegralMixedRoadmapAtomic.payload q) (IntegralMixedRoadmapAtomic.depth q):=by
    unfold finishBirth IntegralMixedRoadmapAtomic.endBirth
    rfl
  have HN:=initial_root hn ht ha hR0 old e
  have HB : b<N old+IntegralMixedCausalRecordPlanBits.count (ROOT old e):=by
    simpa only [fullBirth,HN] using hb1
  have HCount : IntegralMixedCausalRecordPlanBits.count (ROOT old e)=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)):=by
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [midpoint_records hn ht ha hR0 old e []]
  rw [IntegralMixedCausalRecordPlanBits.code,midpoint_records hn ht ha hR0 old e []]
  have HI0 : IntegralMixedRoadmapChain.rawStart (D old) (IntegralMixedRoadmapAtomic.payload q)
      (IntegralMixedRoadmapAtomic.depth q) ≤ b-N old := by omega
  have HI1 : b-N old < WordListRecords.count
      (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) := by
    rw [HCount] at HB
    omega
  exact raw_seed_get HC HP (b-N old) HI0 HI1

theorem seed_active_after_finish (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (b : ℕ)
    (hb0 : finishBirth hn ht ha hR0 old e≤b) (hb1 : b<fullBirth hn ht ha hR0 old e) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) b :=by
  let i:=b-N old
  have HN:=initial_root hn ht ha hR0 old e
  have HI0 : N old≤b:=by
    have H:=finish_eq hn ht ha hR0 old e
    have HL : N old≤beginBirth hn ht ha hR0 old:=by unfold beginBirth IntegralMixedRoadmapAtomic.endBirth;omega
    omega
  have HB : b=number n (ROOT old e)+8+i:=by rw [HN];dsimp only [i];omega
  have HI : i<IntegralMixedCausalRecordPlanBits.count (ROOT old e):=by
    unfold fullBirth at hb1
    rw [HN] at hb1
    dsimp only [i]
    omega
  have HDIM:=dimension_root hn ht ha hR0 old e
  have HG : IntegralMixedChronologicalFrameCode.PointGood
      ((IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)).ambient (ROOT old e))
      (number n (ROOT old e)+8+i) [] 0 0:=empty_point_good _ _
  have HW : IntegralMixedCausalRecordPlanBits.code (ROOT old e) i=
      IntegralMixedChronologicalFrameCode.code
        ((IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)).ambient (ROOT old e)) [] 0 0:=by
    rw [HDIM]
    exact seed_code_after_finish hn ht ha hR0 old hv hd e he b hb0 hb1
  have HA:=frame_active hn ht ha hR0 old e i HI [] 0 0 HG HW
  exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha
    (radius_binary hR0) false (CTX old e) b) HB.symm) HA

theorem active_after_begin (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (b : ℕ)
    (hb0 : beginBirth hn ht ha hR0 old≤b) (hb1 : b<fullBirth hn ht ha hR0 old e) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) b :=by
  by_cases hTail : finishBirth hn ht ha hR0 old e≤b
  · exact seed_active_after_finish hn ht ha hR0 old hv hd e he b hTail hb1
  let a:=beginBirth hn ht ha hR0 old
  let k:=D old-IntegralMixedRoadmapAtomic.depth old
  have HMB:=midpoint_birth hn ht ha hR0 old e
  have HMF : IntegralMixedRoadmapProper.midFirst (D old) (N old) (Q old e)=a+1:=congrArg (fun x=>x+1) HMB
  have HMK:=midpoint_count hn ht ha hR0 old e
  have HCA:=child_anchor hn ht ha hR0 old e
  have HCF : IntegralMixedRoadmapAtomic.first (D old) (N old) (Q old e)=a+2+k:=by
    unfold IntegralMixedRoadmapAtomic.first
    omega
  have HCK:=child_count hn ht ha hR0 old e
  have HFinish:=finish_eq hn ht ha hR0 old e
  dsimp only at HMB HMF HMK HCA HCF HCK HFinish
  by_cases hA : b=a
  · have H:=midpoint_anchor_active hn ht ha hR0 old hv hd e he []
    exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha
      (radius_binary hR0) false (CTX old e) b) (HMB.trans hA.symm)) H
  by_cases hM : b<a+1+k
  · let j:=b-(a+1)
    have HJ : j<IntegralMixedRoadmapProper.captureCount (D old) (Q old e):=by dsimp only [j];omega
    have H:=midpoint_capture_active hn ht ha hR0 old hv hd e he [] j HJ
    have HE : IntegralMixedRoadmapProper.midFirst (D old) (N old) (Q old e)+j=b:=by dsimp only [j];omega
    exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha
      (radius_binary hR0) false (CTX old e) b) HE) H
  by_cases hC : b=a+1+k
  · have H:=child_anchor_active hn ht ha hR0 old hv hd e he
    exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha
      (radius_binary hR0) false (CTX old e) b) (HCA.trans hC.symm)) H
  · let j:=b-(a+2+k)
    have HJ : j<IntegralMixedRoadmapAtomic.free (D old) (Q old e):=by dsimp only [j];omega
    have H:=child_capture_active hn ht ha hR0 old hv hd e he j HJ
    have HE : IntegralMixedRoadmapAtomic.first (D old) (N old) (Q old e)+j=b:=by dsimp only [j];omega
    exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha
      (radius_binary hR0) false (CTX old e) b) HE) H

theorem no_cut_after_begin (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (b : ℕ)
    (hb0 : beginBirth hn ht ha hR0 old≤b) (hb1 : b<fullBirth hn ht ha hR0 old e) :
    ¬IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P PLAN (ROOT old e) b).command :=by
  have HA:=active_after_begin hn ht ha hR0 old hv hd e he b hb0 hb1
  have HCtx:=HA.2
  rw [native_header hn ht ha hR0 old e b] at HCtx
  intro HC
  have HE:=(IntegralFramedCreatingCut.isCut_iff_context _).mp HC
  rw [←IntegralMixedCommandHeaderBits.command_context] at HE
  have HH : IntegralMixedRoadmapSeedMetadata.stageHeader hn ht ha hR0 (ROOT old e) b=
      IntegralMixedCommandHeaderBits.command (IntegralMixedFramedRootPullback.instructionAt P PLAN (ROOT old e) b).command:=by
    unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank IntegralMixedRoadmapSeedMetadata.stageHeader
    rfl
  rw [←HH,HCtx] at HE
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
