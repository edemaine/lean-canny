/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPastCritical
public import LeanCanny.Encoding.IntegralMixedMarkedCutReceipt
public import LeanCanny.Encoding.IntegralMixedMarkedCutReceiptComplete
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixCommands
public import LeanCanny.Encoding.IntegralMixedRoadmapChainRoom
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutValidity
/-! # Literal prefix and full old values preserve historical cut receipts -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem command_heq {a b u v :ℕ}
    (I :IntegralMixedFramedHistoryScript.Instruction a u) (J :IntegralMixedFramedHistoryScript.Instruction b v)
    (ha :a=b) (hb :u=v) (he :HEq I J) :HEq I.command J.command:=by
  subst b;subst v;cases eq_of_heq he;rfl

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" root=>IntegralMixedMarkedPrefixFieldReadback.context root
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.root IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.endBirth
  preparedRoot start IntegralMixedMarkedPrefixObservation.observation IntegralMixedPhysicalFieldEquality.point

private theorem instruction_saved (root :List Bool) (j :ℕ) (hj :j<IntegralMixedCausalRecordPlanBits.count root) :
    HEq (instruction P D (IntegralMixedMarkedCutStage.saved hn ht ha hR0 root (number n root+8+j)))
      (IntegralMixedFramedRootPullback.instructionAt P D root (number n root+8+j)):=by
  let key:=IntegralMixedMarkedCutStage.saved hn ht ha hR0 root (number n root+8+j)
  have HB :number n root+8+j<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount;omega
  have HR :pairFst key=root:=
    (congrArg pairFst (IntegralMixedMarkedCutStage.saved_eq hn ht ha hR0 root _ HB)).trans (keyAt_root _ _ _)
  have HP :prefixLength P key=number n root+8+j:=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H key).symm.trans
      (IntegralMixedMarkedCutStage.saved_birth hn ht ha hR0 root _ HB)
  exact IntegralMixedFramedRootPullback.instructionAt_congr P D _ root _ _ HR HP

private theorem isCut_root (r s :List Bool) (b :ℕ) (hr :r=s) :
    IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D r b).command↔
      IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D s b).command:=
  Iff.of_eq (IntegralMixedFramedRootPullback.instruction_read
    (fun _ _ I=>IntegralFramedCreatingCut.IsCut I.command) _ _
    (congrArg (P).ambient hr) (congrArg (P).width hr)
    (IntegralMixedFramedRootPullback.instructionAt_congr P D r s b b hr rfl))

variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)

/-- The entire cut receipt, including first-nonzero choice, actual degree and
untruncated root, is identical on the two independently sampled histories. -/
theorem past_cut_receipt (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX (preparedRoot hn ht ha hR0 old producer)) w)
    (hr :∀r<IntegralMixedFramedPhysicalIndex.arity (parentCommands hn ht ha hR0 old hv hd producer he),
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (preparedRoot hn ht ha hR0 old producer) w hw r=
        oldNatural hn ht ha hR0 old hv r)
    (j :ℕ) (hj :j<start hn ht ha hR0 old) :
    IntegralMixedMarkedCutStage.ownReceipt hn ht ha hR0 (preparedRoot hn ht ha hR0 old producer) w hw j
      (hj.trans_le ((start_fit hn ht ha hR0 old hv).trans_eq (prepared_count hn ht ha hR0 old hv hd producer he).symm))↔
    IntegralMixedMarkedCutStage.ownReceipt hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old)
      (IntegralMixedRoadmapAtomic.word old) (old_valid_native hn ht ha hR0 old hv) j
      (hj.trans_le (start_fit hn ht ha hR0 old hv)):=by
  let r:=preparedRoot hn ht ha hR0 old producer
  let l:=IntegralMixedRoadmapAtomic.root old
  let kr:=IntegralMixedMarkedCutStage.saved hn ht ha hR0 r (number n r+8+j)
  let kl:=IntegralMixedMarkedCutStage.saved hn ht ha hR0 l (number n l+8+j)
  have HC:=prepared_candidate hn ht ha hR0 old producer
  have HCount:=prepared_count hn ht ha hR0 old hv hd producer he
  have HN :number n r=number n l:=IntegralMixedMarkedPreludeCongruence.number_eq r l HC
  have HJL :j<IntegralMixedCausalRecordPlanBits.count l:=hj.trans_le (start_fit hn ht ha hR0 old hv)
  have HJR :j<IntegralMixedCausalRecordPlanBits.count r:=HJL.trans_eq HCount.symm
  have HCode :∀i,i<j+1→IntegralMixedCausalRecordPlanBits.code r i=IntegralMixedCausalRecordPlanBits.code l i:=by
    intro i hi
    exact prepared_record hn ht ha hR0 old hv producer i (hi.trans_le (Nat.succ_le_of_lt hj))
  have HI0 :HEq (IntegralMixedFramedRootPullback.instructionAt P D r (number n r+8+j))
      (IntegralMixedFramedRootPullback.instructionAt P D l (number n l+8+j)):=by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    exact IntegralMixedMarkedPrefixCommands.creating_heq hn ht ha hR0 r l HC HCount j (Nat.succ_le_of_lt HJR) HCode
  have HI :HEq (instruction P D kr) (instruction P D kl):=
    (instruction_saved hn ht ha hR0 r j HJR).trans (HI0.trans (instruction_saved hn ht ha hR0 l j HJL).symm)
  have HData :IntegralMixedPrefixSnapshot.ofState ((G).state kr)=IntegralMixedPrefixSnapshot.ofState ((G).state kl):=
    (IntegralMixedMarkedCutStage.snapshot_eq hn ht ha hR0 r j HJR).trans
      ((prefix_snapshot hn ht ha hR0 old hv hd producer he j hj.le).trans
        (IntegralMixedMarkedCutStage.snapshot_eq hn ht ha hR0 l j HJL).symm)
  have HCmd :HEq (instruction P D kr).command (instruction P D kl).command:=command_heq _ _
    (congrArg IntegralMixedPrefixSnapshot.Data.ambient HData)
    (congrArg IntegralMixedPrefixSnapshot.Data.width HData) HI
  let vr:=(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 r j HJR.le).point
    (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r w hw)
  let vl:=(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 l j HJL.le).point
    (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 l (IntegralMixedRoadmapAtomic.word old)
      (old_valid_native hn ht ha hR0 old hv))
  let ar:=IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX r) w hw (number n r+8+j)
  let al:=IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX l)
    (IntegralMixedRoadmapAtomic.word old) (old_valid_native hn ht ha hR0 old hv) (number n l+8+j)
  have HRaw:=past_raw_native hn ht ha hR0 old hv hd producer he _ hr
  have HValues :∀i<(G).birth kr,vr i=vl i:=by
    intro i hi
    have HB :number n r+8+j<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r:=by
      unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount;omega
    have HBirth:=(IntegralMixedMarkedCutStage.saved_birth hn ht ha hR0 r (number n r+8+j) HB)
    have HI0 :i<number n l+8+j:=hi.trans_eq (HBirth.trans (congrArg (fun v=>v+8+j) HN))
    exact past_prefix_point hn ht ha hR0 old hv hd producer he _ _ HRaw j hj.le i HI0
  have HA :ar=al:=
    (congrArg (IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX r) w hw)
      (congrArg (fun v=>v+8+j) HN)).trans
        (past_fields hn ht ha hR0 old hv hd producer he w hw hr (number n l+8+j) (by
          change number n l+8+j<number n l+8+start hn ht ha hR0 old
          omega))
  have H0:=IntegralMixedPrefixSnapshot.familyCutReceipt_transport P D H kr kl HData HCmd vr vl ar HValues
  have H1 :IntegralMixedPrefixSnapshot.familyCutReceipt P D H kl vl ar↔
      IntegralMixedPrefixSnapshot.familyCutReceipt P D H kl vl al:=
    Iff.of_eq (congrArg (IntegralMixedPrefixSnapshot.familyCutReceipt P D H kl vl) HA)
  exact H0.trans H1

private theorem length_full (root :List Bool):IntegralFramedTraceCutMetadata.length P D root=
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
  unfold IntegralFramedTraceCutMetadata.length IntegralMixedPhysicalMarkedPlan.bank
  exact IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0 root

private theorem cut_parent_iff (root w :List Bool) (b :ℕ) :
    IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha (radius_binary hR0) false
      (IntegralFramedTraceCutScan.stagePacket (pair root w) b)↔
    IntegralFramedCreatingCut.ParentCut P D (IntegralMixedMarkedCutStage.parent hn ht ha hR0 root b):=by
  change IntegralFramedCreatingCut.ParentCut P D
    (IntegralFramedTraceCutGuards.parent P (IntegralFramedTraceCutScan.stagePacket (pair root w) b))↔_
  have HE:=IntegralMixedPhysicalCutCoefficientSemantics.parent_packet hn ht ha (radius_binary hR0) false root w
    (List.replicate b true)
  simpa only [IntegralFramedTraceCutScan.stagePacket,IntegralMixedPhysicalCutCoefficientSemantics.stage,
    IntegralMixedMarkedCutStage.parent,pairFst_pair,pairSnd_pair] using
      Iff.of_eq (congrArg (IntegralFramedCreatingCut.ParentCut P D) HE)

include hv in
private theorem past_before_bound (b :ℕ)
    (hb :b<number n (IntegralMixedRoadmapAtomic.root old)+8+start hn ht ha hR0 old) :
    b<IntegralMixedPhysicalTraceCutScan.count hn ht ha (radius_binary hR0) false
      (pair (IntegralMixedRoadmapAtomic.root old) (IntegralMixedRoadmapAtomic.word old))-1:=by
  have HC:=IntegralMixedRoadmapAtomic.checked hn ht ha hR0 old hv
  have HCount :IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root old)=
      IntegralMixedRoadmapRecordChain.probedRecordBound (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old):=by
    simpa only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
      IntegralMixedRoadmapAtomic.root,pairFst_pair,pairSnd_pair] using HC.2.2.2.2.2.2.1
  have HStart :start hn ht ha hR0 old≤
      IntegralMixedRoadmapRecordChain.recordBound (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old):=by
    simpa only [start,IntegralMixedRoadmapAtomic.depth] using IntegralMixedRoadmapChain.rawStart_bound
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.payload old)
      (IntegralMixedRoadmapChain.depth (IntegralMixedRoadmapAtomic.payload old)) (HC.1.trans (Nat.le_succ _))
  have HF :(G).birth ((B).key (IntegralMixedPhysicalMarkedTest.sampleContext (IntegralMixedRoadmapAtomic.root old)))=
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (IntegralMixedRoadmapAtomic.root old):=by
    change IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0)
      (IntegralMixedPhysicalMarkedTest.sampleContext (IntegralMixedRoadmapAtomic.root old))=_
    rw [IntegralMixedPhysicalFieldEquality.count_eq]
    simp only [IntegralMixedPhysicalMarkedTest.sampleContext,pairFst_pair]
  rw [←IntegralMixedPhysicalTraceCutValidity.birth_count hn ht ha (radius_binary hR0) false,
    HF,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount,HCount,IntegralMixedRoadmapRecordChain.probedRecordBound]
  omega

/-- Exact historical native cut guards on the new own word, at a raw stage. -/
theorem past_cut_raw_stage (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX (preparedRoot hn ht ha hR0 old producer)) w)
    (hr :∀r<IntegralMixedFramedPhysicalIndex.arity (parentCommands hn ht ha hR0 old hv hd producer he),
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (preparedRoot hn ht ha hR0 old producer) w hw r=
        oldNatural hn ht ha hR0 old hv r)
    (j :ℕ) (hj :j<start hn ht ha hR0 old)
    (hc :IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha (radius_binary hR0) false
      (IntegralFramedTraceCutScan.stagePacket (pair (preparedRoot hn ht ha hR0 old producer) w)
        (number n (IntegralMixedRoadmapAtomic.root old)+8+j))) :
    IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha (radius_binary hR0) false
      (IntegralFramedTraceCutScan.stagePacket (pair (preparedRoot hn ht ha hR0 old producer) w)
        (number n (IntegralMixedRoadmapAtomic.root old)+8+j)):=by
  let r:=preparedRoot hn ht ha hR0 old producer
  let l:=IntegralMixedRoadmapAtomic.root old
  let b:=number n l+8+j
  have HCand:=prepared_candidate hn ht ha hR0 old producer
  have HCount:=prepared_count hn ht ha hR0 old hv hd producer he
  have HN :number n r=number n l:=IntegralMixedMarkedPreludeCongruence.number_eq r l HCand
  have HJL :j<IntegralMixedCausalRecordPlanBits.count l:=hj.trans_le (start_fit hn ht ha hR0 old hv)
  have HJR :j<IntegralMixedCausalRecordPlanBits.count r:=HJL.trans_eq HCount.symm
  have HCode :∀i,i<j+1→IntegralMixedCausalRecordPlanBits.code r i=IntegralMixedCausalRecordPlanBits.code l i:=by
    intro i hi
    exact prepared_record hn ht ha hR0 old hv producer i (hi.trans_le (Nat.succ_le_of_lt hj))
  have HCnew :IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha (radius_binary hR0) false
      (IntegralFramedTraceCutScan.stagePacket (pair r w) (number n r+8+j)):=by
    simpa only [HN] using hc
  have HIn :=(IntegralFramedTraceCutOrigin.stageCut_iff P D (pair r w) (number n r+8+j) (by
    simp only [pairFst_pair,length_full hn ht ha hR0]
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount;omega)).mp HCnew
  have HInR :=(isCut_root hn ht ha hR0 (pairFst (pair r w)) r _ (pairFst_pair _ _)).mp HIn
  have HH:=IntegralMixedMarkedPrefixCriticalMetadata.header_eq hn ht ha hR0 r l HCand HCount j
    (Nat.succ_le_of_lt HJR) HCode
  have HCtx :(IntegralMixedFramedRootPullback.instructionAt P D r (number n r+8+j)).command.context=
      (IntegralMixedFramedRootPullback.instructionAt P D l b).command.context:=by
    simpa only [IntegralMixedMarkedPrefixCriticalMetadata.header_actual,IntegralMixedCommandHeaderBits.command_context]
      using congrArg IntegralMixedCommandHeaderBits.Header.context HH
  have HInOld :IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D l b).command:=
    (IntegralFramedCreatingCut.isCut_iff_context _).mpr
      (((IntegralFramedCreatingCut.isCut_iff_context _).mp HInR).trans_eq HCtx)
  have HCold :IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha (radius_binary hR0) false
      (IntegralFramedTraceCutScan.stagePacket (pair l (IntegralMixedRoadmapAtomic.word old)) b):=by
    apply (IntegralFramedTraceCutOrigin.stageCut_iff P D (pair l (IntegralMixedRoadmapAtomic.word old)) b (by
      simp only [pairFst_pair,length_full hn ht ha hR0]
      unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
      dsimp only [b];omega)).mpr
    exact (isCut_root hn ht ha hR0 (pairFst (pair l (IntegralMixedRoadmapAtomic.word old))) l b
      (pairFst_pair _ _)).mpr HInOld
  have HBefore :IntegralMixedPhysicalTraceBeforeProbe.holds hn ht ha (radius_binary hR0) false
      (pair l (IntegralMixedRoadmapAtomic.word old)):=hv.2.2.2.1.2
  have HOldGuard:=HBefore b (past_before_bound hn ht ha hR0 old hv b (by
    change number n l+8+j<number n l+8+start hn ht ha hR0 old;omega)) HCold
  have HOldReceipt:=IntegralMixedMarkedCutStage.ownReceipt_of_guard hn ht ha hR0 l
    (IntegralMixedRoadmapAtomic.word old) (old_valid_native hn ht ha hR0 old hv) j HJL
    ((cut_parent_iff hn ht ha hR0 l _ b).mp HCold) (by
      simpa only [IntegralFramedTraceCutScan.stagePacket,IntegralMixedPhysicalCutCoefficientSemantics.stage,
        pairFst_pair,pairSnd_pair] using HOldGuard)
  have HNewReceipt:=(past_cut_receipt hn ht ha hR0 old hv hd producer he w hw hr j hj).mpr HOldReceipt
  have HNew:=IntegralMixedMarkedCutStage.guard_of_ownReceipt hn ht ha hR0 r w hw j HJR
    ((cut_parent_iff hn ht ha hR0 r w (number n r+8+j)).mp HCnew) HNewReceipt
  simpa only [IntegralFramedTraceCutScan.stagePacket,IntegralMixedPhysicalCutCoefficientSemantics.stage,
    pairFst_pair,pairSnd_pair,HN] using HNew

/-- Every historical creating cut is checked on the new full word. The
integer prelude is excluded by its actual command, not a factor fallback. -/
theorem past_cut (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX (preparedRoot hn ht ha hR0 old producer)) w)
    (hr :∀r<IntegralMixedFramedPhysicalIndex.arity (parentCommands hn ht ha hR0 old hv hd producer he),
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (preparedRoot hn ht ha hR0 old producer) w hw r=
        oldNatural hn ht ha hR0 old hv r)
    (b :ℕ) (hb :b<number n (IntegralMixedRoadmapAtomic.root old)+8+start hn ht ha hR0 old)
    (hc :IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha (radius_binary hR0) false
      (IntegralFramedTraceCutScan.stagePacket (pair (preparedRoot hn ht ha hR0 old producer) w) b)) :
    IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha (radius_binary hR0) false
      (IntegralFramedTraceCutScan.stagePacket (pair (preparedRoot hn ht ha hR0 old producer) w) b):=by
  let r:=preparedRoot hn ht ha hR0 old producer
  have HN :number n r=number n (IntegralMixedRoadmapAtomic.root old):=
    IntegralMixedMarkedPreludeCongruence.number_eq _ _ (prepared_candidate hn ht ha hR0 old producer)
  by_cases hp:b<number n r+8
  · have HIn :=(IntegralFramedTraceCutOrigin.stageCut_iff P D (pair r w) b (by
      simp only [pairFst_pair,length_full hn ht ha hR0]
      unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount;omega)).mp hc
    have HInR:=(isCut_root hn ht ha hR0 (pairFst (pair r w)) r b (pairFst_pair _ _)).mp HIn
    have HH :IntegralMixedCommandHeaderBits.command (IntegralMixedFramedRootPullback.instructionAt P D r b).command=
        IntegralMixedCommandHeaderBits.zero:=by
      unfold IntegralMixedPhysicalMarkedPlan.bank
      exact IntegralMixedRoadmapSeedMetadata.prelude_header hn ht ha hR0 r b hp
    have HZero :(IntegralMixedFramedRootPullback.instructionAt P D r b).command.context=0:=by
      simpa only [IntegralMixedCommandHeaderBits.command_context,IntegralMixedCommandHeaderBits.zero]
        using congrArg IntegralMixedCommandHeaderBits.Header.context HH
    have HGE:=(IntegralFramedCreatingCut.isCut_iff_context _).mp HInR
    omega
  · have HL :number n (IntegralMixedRoadmapAtomic.root old)+8≤b:=by rw [HN] at hp;omega
    obtain ⟨j,HJ⟩:=Nat.exists_eq_add_of_le HL
    subst b
    exact past_cut_raw_stage hn ht ha hR0 old hv hd producer he w hw hr j (by omega) hc

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
