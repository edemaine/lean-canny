/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedProperMetadata
public import LeanCanny.Encoding.IntegralMixedRoadmapChainSeedTail
public import LeanCanny.Encoding.IntegralFramedCreatingCut
/-! # A checked latest level has a critical-only tail after its midpoint -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapCheckedCriticalTail
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedRoadmapCheckedProperMetadata
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

/-- Latest block lengths do not depend on the fresh endpoints before the midpoint. -/
theorem latest_layout {d initial :ℕ} {q :List Bool}
    (H :IntegralMixedRoadmapAtomic.depth q≤d) (hd :0<IntegralMixedRoadmapAtomic.depth q) :
    IntegralMixedRoadmapAtomic.endBirth d initial q=
      IntegralMixedRoadmapProper.midBirth d initial q+2+2*IntegralMixedRoadmapProper.captureCount d q ∧
    IntegralMixedRoadmapAtomic.free d q=IntegralMixedRoadmapProper.captureCount d q ∧
    IntegralMixedRoadmapAtomic.anchor d initial q=
      IntegralMixedRoadmapProper.midBirth d initial q+1+IntegralMixedRoadmapProper.captureCount d q:=by
  have HE :IntegralMixedRoadmapAtomic.depth q=IntegralMixedRoadmapProper.levelIndex q+1:=by
    unfold IntegralMixedRoadmapProper.levelIndex
    omega
  have HR:=IntegralMixedRoadmapChain.rawStart_succ d (IntegralMixedRoadmapAtomic.payload q)
    (IntegralMixedRoadmapProper.levelIndex q)
  have HF :IntegralMixedRoadmapAtomic.free d q=IntegralMixedRoadmapProper.captureCount d q:=by
    unfold IntegralMixedRoadmapAtomic.free IntegralMixedRoadmapProper.captureCount
    omega
  have HB :IntegralMixedRoadmapAtomic.endBirth d initial q=
      IntegralMixedRoadmapProper.midBirth d initial q+2+2*IntegralMixedRoadmapProper.captureCount d q:=by
    unfold IntegralMixedRoadmapAtomic.endBirth
    rw [HE,HR]
    unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth
      IntegralMixedRoadmapChain.birth IntegralMixedRoadmapChain.blockCount IntegralMixedRoadmapProper.captureCount
    omega
  refine ⟨HB,HF,?_⟩
  unfold IntegralMixedRoadmapAtomic.anchor
  rw [HB,HF]
  omega

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "I"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.root
  IntegralMixedRoadmapAtomic.context IntegralMixedRoadmapSeedMetadata.stageHeader
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerSource.source
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
variable (q :List Bool)
  (H :IntegralMixedRoadmapChain.Checked (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
    (IntegralMixedRoadmapAtomic.width hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 q)
    (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha q)
    (IntegralMixedRoadmapAtomic.payload q))
  (hp :IntegralMixedRoadmapChain.probe (IntegralMixedRoadmapAtomic.payload q)=
    IntegralMixedRoadmapChain.seedCode (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q))

include H hp in
/-- Literal seed padding includes the reserved final probe. -/
theorem seed_code_after_end (b :ℕ)
    (hb0 :IntegralMixedRoadmapAtomic.endBirth (D q) (I q) q≤b)
    (hb1 :b<IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (IntegralMixedRoadmapAtomic.context q))) :
    IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root q) (b-I q)=
      IntegralMixedRoadmapChain.seedCode (D q):=by
  rw [full_prefix hn ht ha hR0 q] at hb1
  unfold IntegralMixedCausalRecordPlanBits.code
  rw [root_records q]
  unfold IntegralMixedRoadmapAtomic.endBirth at hb0
  apply raw_seed_get H hp (b-I q) ?_ (by omega)
  change IntegralMixedRoadmapChain.rawStart (D q) (IntegralMixedRoadmapAtomic.payload q)
    (IntegralMixedRoadmapAtomic.depth q)≤b-I q
  omega

include H hp in
theorem seed_active_after_end (b :ℕ)
    (hb0 :IntegralMixedRoadmapAtomic.endBirth (D q) (I q) q≤b)
    (hb1 :b<IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (IntegralMixedRoadmapAtomic.context q))) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) b:=by
  have HI0 :I q≤b:=by unfold IntegralMixedRoadmapAtomic.endBirth at hb0;omega
  let i:=b-I q
  have HB :b=number n (IntegralMixedRoadmapAtomic.root q)+8+i:=by
    rw [root_initial hn ht ha hR0 q]
    dsimp only [i]
    omega
  have HI :i<IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q):=by
    rw [full_prefix hn ht ha hR0 q] at hb1
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [root_records q]
    dsimp only [i]
    omega
  have HG :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (IntegralMixedRoadmapAtomic.root q))
      (number n (IntegralMixedRoadmapAtomic.root q)+8+i) [] 0 0:=empty_point_good _ _
  have HW :IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root q) i=
      IntegralMixedChronologicalFrameCode.code ((P).ambient (IntegralMixedRoadmapAtomic.root q)) [] 0 0:=by
    rw [root_dimension hn ht ha hR0 q]
    exact seed_code_after_end hn ht ha hR0 q H hp b hb0 hb1
  have HC:=IntegralMixedMarkedRecordReceipt.critical hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q) i HI [] 0 0 HG HW
  constructor
  · simpa only [IntegralFramedPhysicalCriticalGuardScan.stage,pairSnd_pair,List.length_replicate,
      IntegralFramedPhysicalCriticalGuardTest.keyDatum,pairFst_pair] using hb1
  · rw [native_header hn ht ha hR0 q]
    rw [HB]
    unfold IntegralMixedRoadmapSeedMetadata.stageHeader
    exact congrArg (fun c=>(IntegralMixedCommandHeaderBits.command c).context) HC

variable (hd :0<IntegralMixedRoadmapAtomic.depth q)

include H hd hp in
/-- Fresh endpoint cuts may occur before this boundary; every stage at or after
this latest midpoint is genuinely critical, including padding and the probe. -/
theorem active_after_mid (b :ℕ)
    (hb0 :IntegralMixedRoadmapProper.midBirth (D q) (I q) q≤b)
    (hb1 :b<IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (IntegralMixedRoadmapAtomic.context q))) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) b:=by
  by_cases hTail :IntegralMixedRoadmapAtomic.endBirth (D q) (I q) q≤b
  · exact seed_active_after_end hn ht ha hR0 q H hp b hTail hb1
  have HL:=latest_layout (initial:=I q) H.1 hd
  let a:=IntegralMixedRoadmapProper.midBirth (D q) (I q) q
  let c:=IntegralMixedRoadmapProper.captureCount (D q) q
  have HMF :IntegralMixedRoadmapProper.midFirst (D q) (I q) q=a+1:=rfl
  have HCF :IntegralMixedRoadmapAtomic.first (D q) (I q) q=a+2+c:=by
    unfold IntegralMixedRoadmapAtomic.first
    dsimp only [a,c]
    omega
  by_cases hA :b=a
  · exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha
      (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q) b) hA.symm)
      (midpoint_anchor hn ht ha hR0 q H hd).1
  by_cases hM :b<a+1+c
  · let j:=b-(a+1)
    have HJ :j<IntegralMixedRoadmapProper.captureCount (D q) q:=by dsimp only [j,c] at *;omega
    have HA:=(midpoint_capture hn ht ha hR0 q H hd j HJ).1
    have HE :IntegralMixedRoadmapProper.midFirst (D q) (I q) q+j=b:=by dsimp only [j];omega
    exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha
      (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q) b) HE) HA
  by_cases hC :b=a+1+c
  · have HE :IntegralMixedRoadmapAtomic.anchor (D q) (I q) q=b:=HL.2.2.trans hC.symm
    exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha
      (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q) b) HE)
      (child_anchor hn ht ha hR0 q H hd).1
  · let j:=b-(a+2+c)
    have HJ :j<IntegralMixedRoadmapAtomic.free (D q) q:=by dsimp only [j,a,c] at *;omega
    have HA:=(child_capture hn ht ha hR0 q H j HJ).1
    have HE :IntegralMixedRoadmapAtomic.first (D q) (I q) q+j=b:=by dsimp only [j];omega
    exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha
      (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q) b) HE) HA

include H hd hp in
/-- The actual creating header, useful for physical-prefix arity sums. -/
theorem header_after_mid (b :ℕ)
    (hb0 :IntegralMixedRoadmapProper.midBirth (D q) (I q) q≤b)
    (hb1 :b<IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (IntegralMixedRoadmapAtomic.context q))) :
    (IntegralMixedRoadmapSeedMetadata.stageHeader hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q) b).context=1:=by
  have HC:=(active_after_mid hn ht ha hR0 q H hp hd b hb0 hb1).2
  rw [native_header hn ht ha hR0 q] at HC
  exact HC

include H hd hp in
theorem no_cut_after_mid (b :ℕ)
    (hb0 :IntegralMixedRoadmapProper.midBirth (D q) (I q) q≤b)
    (hb1 :b<IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (IntegralMixedRoadmapAtomic.context q))) :
    ¬IntegralFramedCreatingCut.IsCut
      (IntegralMixedFramedRootPullback.instructionAt P PLAN (IntegralMixedRoadmapAtomic.root q) b).command:=by
  have HCtx:=(active_after_mid hn ht ha hR0 q H hp hd b hb0 hb1).2
  rw [native_header hn ht ha hR0 q] at HCtx
  intro HC
  have HE:=(IntegralFramedCreatingCut.isCut_iff_context _).mp HC
  rw [←IntegralMixedCommandHeaderBits.command_context] at HE
  have HH :IntegralMixedRoadmapSeedMetadata.stageHeader hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q) b=
      IntegralMixedCommandHeaderBits.command
        (IntegralMixedFramedRootPullback.instructionAt P PLAN (IntegralMixedRoadmapAtomic.root q) b).command:=by
    unfold IntegralMixedRoadmapSeedMetadata.stageHeader
    rfl
  rw [←HH,HCtx] at HE
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapCheckedCriticalTail
