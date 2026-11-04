/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedMidpoint
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedChild
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedHeader
public import LeanCanny.Encoding.IntegralMixedMarkedMidpointReceipt
public import LeanCanny.Geometry.IntegralMixedChronologicalMidpointCriticalReadback
/-! # Proper-level native metadata follows from checked bytes alone -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapCheckedProperMetadata
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
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "I"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.root IntegralMixedRoadmapAtomic.context
  IntegralMixedRoadmapSeedMetadata.stageHeader IntegralMixedFramedRootPullback.instructionAt
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerSource.source
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus

private theorem stage_packet (c :List Bool) (b :ℕ) :
    IntegralFramedPhysicalCriticalGuardScan.stage (pair c (List.replicate b true))=b :=by
  rw [IntegralFramedPhysicalCriticalGuardScan.stage,pairSnd_pair,List.length_replicate]
private theorem datum_packet (f :List Bool→List Bool) (c :List Bool) (b :ℕ) :
    IntegralFramedPhysicalCriticalGuardTest.keyDatum f (pair c (List.replicate b true))=f c :=
  congrArg f (pairFst_pair _ _)

theorem root_dimension (q :List Bool) :(P).ambient (IntegralMixedRoadmapAtomic.root q)=D q :=by
  change number n (IntegralMixedRoadmapAtomic.root q)+3=_
  rw [IntegralMixedRoadmapAtomic.dimension_eq]
  simp only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,
    pairFst_pair,IntegralMixedRoadmapAtomic.original]
theorem root_initial (q :List Bool) :number n (IntegralMixedRoadmapAtomic.root q)+8=I q :=by
  rw [IntegralMixedRoadmapAtomic.initial_eq]
  simp only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,
    pairFst_pair,IntegralMixedRoadmapAtomic.original]
theorem root_records (q :List Bool) :IntegralMixedCausalRecordPlanBits.records (IntegralMixedRoadmapAtomic.root q)=
    IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q) :=by
  simp only [IntegralMixedCausalRecordPlanBits.records,IntegralMixedRoadmapAtomic.root,pairFst_pair,pairSnd_pair]

theorem full_prefix (q :List Bool) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (IntegralMixedRoadmapAtomic.context q))=
      I q+WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) :=by
  have HC:=IntegralMixedPhysicalFieldEquality.count_eq hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context q)
  simp only [IntegralMixedRoadmapAtomic.context,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount] at HC
  rw [root_initial hn ht ha hR0 q] at HC
  unfold IntegralMixedCausalRecordPlanBits.count at HC
  rw [root_records q] at HC
  have HC' :IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context q)=I q+
        WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) :=by
    simpa only [IntegralMixedRoadmapAtomic.context] using HC
  exact (IntegralMixedFramedHistoryFamilyBits.family_birth (B).parameters (B).plan (B).data _).symm.trans HC'

theorem native_header (q :List Bool) (b :ℕ) :
    IntegralMixedFramedCriticalGuardBits.header T (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key)
      IntegralFramedPhysicalCriticalGuardScan.stage (pair (IntegralMixedRoadmapAtomic.context q) (List.replicate b true))=
        IntegralMixedRoadmapSeedMetadata.stageHeader hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q) b :=by
  rw [IntegralMixedFramedCriticalGuardBits.header_actual (B).parameters (B).plan (B).data T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false)]
  rw [datum_packet,stage_packet,IntegralMixedPhysicalFieldEquality.key_root hn ht ha (radius_binary hR0),
    IntegralMixedRoadmapAtomic.context,pairFst_pair]
  unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank
    IntegralMixedRoadmapSeedMetadata.stageHeader
  rfl

private theorem active_of_context (q :List Bool) (b :ℕ)
    (hb :b<I q+WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)))
    (hc :(IntegralMixedRoadmapSeedMetadata.stageHeader hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q) b).context=1) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q) b :=by
  constructor
  · rw [datum_packet,stage_packet,full_prefix hn ht ha hR0 q]
    exact hb
  · rw [native_header]
    exact hc

private theorem frame_code_metadata (q :List Bool) (i :ℕ)
    (hi :i<IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q)) (labels :List Bool) (g j :ℕ)
    (hg :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (IntegralMixedRoadmapAtomic.root q))
      (number n (IntegralMixedRoadmapAtomic.root q)+8+i) labels g j)
    (hw :IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root q) i=
      IntegralMixedChronologicalFrameCode.code ((P).ambient (IntegralMixedRoadmapAtomic.root q)) labels g j) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (number n (IntegralMixedRoadmapAtomic.root q)+8+i) ∧
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (number n (IntegralMixedRoadmapAtomic.root q)+8+i)=j :=by
  have HCount :IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q)=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) :=by
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [root_records q]
  have HC:=IntegralMixedMarkedRecordReceipt.critical hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q) i hi labels g j hg hw
  refine ⟨?_,?_⟩
  · apply active_of_context hn ht ha hR0 q _ (by rw [root_initial hn ht ha hR0 q];rw [HCount] at hi;omega)
    unfold IntegralMixedRoadmapSeedMetadata.stageHeader
    exact congrArg (fun c=>(IntegralMixedCommandHeaderBits.command c).context) HC
  · unfold IntegralMixedPhysicalPointCompanionScan.selected
    rw [native_header hn ht ha hR0 q]
    unfold IntegralMixedRoadmapSeedMetadata.stageHeader
    rw [HC]
    exact IntegralMixedChronologicalFrame.raw_selected _ labels g j hg

private theorem frame_record_metadata (q :List Bool) (b :ℕ)
    (hb0 :I q≤b) (hb1 :b<I q+WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)))
    (labels :List Bool) (g j :ℕ)
    (hg :IntegralMixedChronologicalFrameCode.PointGood (D q) b labels g j)
    (hw :WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) (b-I q)=
      IntegralMixedChronologicalFrameCode.code (D q) labels g j) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q) b ∧
      IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q) b=j :=by
  let i:=b-I q
  have HB :b=number n (IntegralMixedRoadmapAtomic.root q)+8+i :=by rw [root_initial hn ht ha hR0 q];dsimp only [i];omega
  have HI :i<IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q) :=by
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [root_records q]
    dsimp only [i]
    omega
  have HN:=root_dimension hn ht ha hR0 q
  have HG :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (IntegralMixedRoadmapAtomic.root q))
      (number n (IntegralMixedRoadmapAtomic.root q)+8+i) labels g j :=
    Eq.mp (congrArg₂ (fun d b=>IntegralMixedChronologicalFrameCode.PointGood d b labels g j) HN.symm HB) hg
  have HW :IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root q) i=
      IntegralMixedChronologicalFrameCode.code ((P).ambient (IntegralMixedRoadmapAtomic.root q)) labels g j :=by
    rw [IntegralMixedCausalRecordPlanBits.code,root_records q,HN]
    exact hw
  have H:=frame_code_metadata hn ht ha hR0 q i HI labels g j HG HW
  exact ⟨Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha
      (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q) b) HB.symm) H.1,
    (congrArg (IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q)) HB).trans H.2⟩

private theorem midpoint_code_metadata (q :List Bool) (i :ℕ)
    (hi :i<IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q)) (labels :List Bool) (a c :ℕ) (g j :ℕ)
    (hg :IntegralMixedChronologicalMidpointCode.Good ((P).ambient (IntegralMixedRoadmapAtomic.root q))
      (number n (IntegralMixedRoadmapAtomic.root q)+8+i) labels a c g j)
    (hw :IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root q) i=
      IntegralMixedChronologicalMidpointCode.code ((P).ambient (IntegralMixedRoadmapAtomic.root q)) labels a c g j) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (number n (IntegralMixedRoadmapAtomic.root q)+8+i) ∧
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (number n (IntegralMixedRoadmapAtomic.root q)+8+i)=j :=by
  have HCount :IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q)=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) :=by
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [root_records q]
  have HC:=IntegralMixedMarkedMidpointReceipt.critical hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q) i hi labels a c g j hg hw
  refine ⟨?_,?_⟩
  · apply active_of_context hn ht ha hR0 q _ (by rw [root_initial hn ht ha hR0 q];rw [HCount] at hi;omega)
    unfold IntegralMixedRoadmapSeedMetadata.stageHeader
    exact congrArg (fun c=>(IntegralMixedCommandHeaderBits.command c).context) HC
  · unfold IntegralMixedPhysicalPointCompanionScan.selected
    rw [native_header hn ht ha hR0 q]
    unfold IntegralMixedRoadmapSeedMetadata.stageHeader
    rw [HC]
    exact IntegralMixedChronologicalMidpoint.raw_selected _ labels a c g j hg

private theorem midpoint_record_metadata (q :List Bool) (b :ℕ)
    (hb0 :I q≤b) (hb1 :b<I q+WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)))
    (labels :List Bool) (a c :ℕ) (g j :ℕ)
    (hg :IntegralMixedChronologicalMidpointCode.Good (D q) b labels a c g j)
    (hw :WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) (b-I q)=
      IntegralMixedChronologicalMidpointCode.code (D q) labels a c g j) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q) b ∧
      IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q) b=j :=by
  let i:=b-I q
  have HB :b=number n (IntegralMixedRoadmapAtomic.root q)+8+i :=by rw [root_initial hn ht ha hR0 q];dsimp only [i];omega
  have HI :i<IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q) :=by
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [root_records q]
    dsimp only [i]
    omega
  have HN:=root_dimension hn ht ha hR0 q
  have HG :IntegralMixedChronologicalMidpointCode.Good ((P).ambient (IntegralMixedRoadmapAtomic.root q))
      (number n (IntegralMixedRoadmapAtomic.root q)+8+i) labels a c g j :=
    Eq.mp (congrArg₂ (fun d b=>IntegralMixedChronologicalMidpointCode.Good d b labels a c g j) HN.symm HB) hg
  have HW :IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root q) i=
      IntegralMixedChronologicalMidpointCode.code ((P).ambient (IntegralMixedRoadmapAtomic.root q)) labels a c g j :=by
    rw [IntegralMixedCausalRecordPlanBits.code,root_records q,HN]
    exact hw
  have H:=midpoint_code_metadata hn ht ha hR0 q i HI labels a c g j HG HW
  exact ⟨Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha
      (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q) b) HB.symm) H.1,
    (congrArg (IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q)) HB).trans H.2⟩

private theorem midpoint_birth_eq (d initial :ℕ) (q :List Bool) :
    IntegralMixedRoadmapProper.midBirth d initial q=initial+IntegralMixedRoadmapProper.midRawIndex d q :=by
  unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth
    IntegralMixedRoadmapChain.birth IntegralMixedRoadmapProper.midRawIndex
  omega

variable (q :List Bool)
    (H :IntegralMixedRoadmapChain.Checked (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha q)
      (IntegralMixedRoadmapAtomic.payload q))
    (hd :0<IntegralMixedRoadmapAtomic.depth q)

include H hd in
theorem midpoint_anchor :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapProper.midBirth (D q) (I q) q) ∧
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapProper.midBirth (D q) (I q) q)=IntegralMixedRoadmapProper.levelIndex q+1 :=by
  have HB:=midpoint_birth_eq (D q) (I q) q
  have HF:=IntegralMixedRoadmapProper.checked_midpoint_fit H hd
  apply midpoint_record_metadata hn ht ha hR0 q _ (by rw [HB];omega) (by rw [HB];omega)
    _ _ _ _ _ (IntegralMixedRoadmapProper.checked_midpoint_good H hd)
  rw [HB,Nat.add_sub_cancel_left]
  exact IntegralMixedRoadmapProper.checked_midpoint_record H hd

include H hd in
theorem midpoint_capture (i :ℕ) (hi :i<IntegralMixedRoadmapProper.captureCount (D q) q) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapProper.midFirst (D q) (I q) q+i) ∧
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapProper.midFirst (D q) (I q) q+i)=D q-i :=by
  have HB :IntegralMixedRoadmapProper.midFirst (D q) (I q) q+i=
      I q+(IntegralMixedRoadmapProper.midRawIndex (D q) q+1+i) :=by
    unfold IntegralMixedRoadmapProper.midFirst
    rw [midpoint_birth_eq]
    omega
  have HF:=IntegralMixedRoadmapProper.checked_midpoint_companion_fit H hd i hi
  apply midpoint_record_metadata hn ht ha hR0 q _ (by rw [HB];omega) (by rw [HB];omega)
    _ _ _ _ _ (IntegralMixedRoadmapProper.checked_midpoint_companion_good H hd i hi)
  rw [HB,Nat.add_sub_cancel_left]
  exact IntegralMixedRoadmapProper.checked_midpoint_companion_record H hd i hi

include H in
private theorem child_bounds :
    I q≤IntegralMixedRoadmapAtomic.anchor (D q) (I q) q ∧
    IntegralMixedRoadmapAtomic.anchor (D q) (I q) q<IntegralMixedRoadmapAtomic.endBirth (D q) (I q) q ∧
    IntegralMixedRoadmapAtomic.endBirth (D q) (I q) q<I q+
      WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) :=by
  have HD :IntegralMixedRoadmapAtomic.depth q≤D q:=H.1
  have HR :D q+2≤IntegralMixedRoadmapChain.rawStart (D q) (IntegralMixedRoadmapAtomic.payload q)
      (IntegralMixedRoadmapAtomic.depth q) :=by unfold IntegralMixedRoadmapChain.rawStart;omega
  have HU:=IntegralMixedRoadmapChain.rawStart_bound (D q) (IntegralMixedRoadmapAtomic.payload q)
    (IntegralMixedRoadmapAtomic.depth q) (by omega)
  have HC:=H.2.2.2.2.2.2.1
  have HE:=IntegralMixedRoadmapAtomic.block_end (D q) (I q) q HD
  refine ⟨?_,?_,?_⟩
  · unfold IntegralMixedRoadmapAtomic.anchor IntegralMixedRoadmapAtomic.endBirth IntegralMixedRoadmapAtomic.free
    omega
  · unfold IntegralMixedRoadmapAtomic.first at HE
    omega
  · unfold IntegralMixedRoadmapAtomic.endBirth
    rw [HC]
    unfold IntegralMixedRoadmapRecordChain.probedRecordBound
    omega

include H hd in
theorem child_anchor :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapAtomic.anchor (D q) (I q) q) ∧
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapAtomic.anchor (D q) (I q) q)=IntegralMixedRoadmapAtomic.depth q :=by
  have HB:=child_bounds hn ht ha hR0 q H
  apply frame_record_metadata hn ht ha hR0 q _ HB.1 (HB.2.1.trans HB.2.2)
    _ _ _ (IntegralMixedRoadmapAtomic.anchor_point_good H)
  exact IntegralMixedRoadmapAtomic.checked_anchor_record H hd

include H in
theorem child_capture (i :ℕ) (hi :i<IntegralMixedRoadmapAtomic.free (D q) q) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapAtomic.first (D q) (I q) q+i) ∧
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapAtomic.first (D q) (I q) q+i)=D q-i :=by
  have HB:=child_bounds hn ht ha hR0 q H
  have HD :IntegralMixedRoadmapAtomic.depth q≤D q:=H.1
  have HE:=IntegralMixedRoadmapAtomic.block_end (D q) (I q) q HD
  have HF :I q≤IntegralMixedRoadmapAtomic.first (D q) (I q) q :=by
    unfold IntegralMixedRoadmapAtomic.first
    omega
  apply frame_record_metadata hn ht ha hR0 q _ (by omega) (by omega)
    _ _ _ (IntegralMixedRoadmapAtomic.capture_point_good H i hi)
  have HI :IntegralMixedRoadmapAtomic.first (D q) (I q) q+i-I q=
      IntegralMixedRoadmapAtomic.first (D q) (I q) q-I q+i :=by omega
  rw [HI]
  exact IntegralMixedRoadmapAtomic.latest_capture_record H i hi

end LeanCanny.Encoding.IntegralMixedRoadmapCheckedProperMetadata
