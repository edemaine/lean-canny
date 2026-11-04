/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendReadback
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedHeader
public import LeanCanny.Encoding.IntegralMixedMarkedMidpointReceipt
/-! # Literal critical commands activate the appended word's native queries -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "ROOT"=>preparedRoot hn ht ha hR0
local notation "CTX"=>context hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial preparedRoot context IntegralMixedRoadmapSeedMetadata.stageHeader
  IntegralMixedFramedRootPullback.instructionAt IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedFramedRawHeight.rootCeiling
  IntegralMixedFramedNormalizationBits.requiredModulus

private theorem stage_packet (c : List Bool) (b : ℕ) :
    IntegralFramedPhysicalCriticalGuardScan.stage (pair c (List.replicate b true))=b:=by
  rw [IntegralFramedPhysicalCriticalGuardScan.stage,pairSnd_pair,List.length_replicate]

private theorem datum_packet (f : List Bool→List Bool) (c : List Bool) (b : ℕ) :
    IntegralFramedPhysicalCriticalGuardTest.keyDatum f (pair c (List.replicate b true))=f c:=
  congrArg f (pairFst_pair _ _)

theorem dimension_root (old : List Bool) (e : ℕ) :
    (P).ambient (ROOT old e)=IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old:=by
  change number n (ROOT old e)+3=_
  rw [IntegralMixedRoadmapAtomic.dimension_eq]
  simp only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,preparedRoot,IntegralMixedRoadmapAtomic.root,
    candidate_packet,pairFst_pair,IntegralMixedRoadmapAtomic.original]

theorem initial_root (old : List Bool) (e : ℕ) :
    number n (ROOT old e)+8=IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old:=by
  rw [IntegralMixedRoadmapAtomic.initial_eq]
  simp only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,preparedRoot,IntegralMixedRoadmapAtomic.root,
    candidate_packet,pairFst_pair,IntegralMixedRoadmapAtomic.original]

theorem native_header (old : List Bool) (e b : ℕ) :
    IntegralMixedFramedCriticalGuardBits.header T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
      (pair (CTX old e) (List.replicate b true))=
        IntegralMixedRoadmapSeedMetadata.stageHeader hn ht ha hR0 (ROOT old e) b:=by
  rw [IntegralMixedFramedCriticalGuardBits.header_actual (B).parameters (B).plan (B).data T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false)]
  rw [datum_packet,stage_packet]
  rw [IntegralMixedPhysicalFieldEquality.key_root hn ht ha (radius_binary hR0),context,pairFst_pair]
  unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank
    IntegralMixedRoadmapSeedMetadata.stageHeader
  rfl

theorem active_of_context (old : List Bool) (e b : ℕ)
    (hb : b<fullBirth hn ht ha hR0 old e)
    (hc : (IntegralMixedRoadmapSeedMetadata.stageHeader hn ht ha hR0 (ROOT old e) b).context=1) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) b:=by
  constructor
  · rw [datum_packet,stage_packet]
    rw [prefix_length]
    exact hb
  · rw [native_header]
    exact hc

theorem frame_active (old : List Bool) (e a : ℕ)
    (ha0 : a<IntegralMixedCausalRecordPlanBits.count (ROOT old e)) (labels : List Bool) (g j : ℕ)
    (hg : IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (ROOT old e))
      (number n (ROOT old e)+8+a) labels g j)
    (hw : IntegralMixedCausalRecordPlanBits.code (ROOT old e) a=
      IntegralMixedChronologicalFrameCode.code ((P).ambient (ROOT old e)) labels g j) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e)
      (number n (ROOT old e)+8+a):=by
  apply active_of_context hn ht ha hR0 old e _ (by unfold fullBirth;omega)
  have H:=IntegralMixedMarkedRecordReceipt.critical hn ht ha hR0 (ROOT old e) a ha0 labels g j hg hw
  unfold IntegralMixedRoadmapSeedMetadata.stageHeader
  exact congrArg (fun c=>(IntegralMixedCommandHeaderBits.command c).context) H

theorem midpoint_active (old : List Bool) (e i : ℕ)
    (hi : i<IntegralMixedCausalRecordPlanBits.count (ROOT old e)) (labels : List Bool) (a b g j : ℕ)
    (hg : IntegralMixedChronologicalMidpointCode.Good ((P).ambient (ROOT old e))
      (number n (ROOT old e)+8+i) labels a b g j)
    (hw : IntegralMixedCausalRecordPlanBits.code (ROOT old e) i=
      IntegralMixedChronologicalMidpointCode.code ((P).ambient (ROOT old e)) labels a b g j) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e)
      (number n (ROOT old e)+8+i):=by
  apply active_of_context hn ht ha hR0 old e _ (by unfold fullBirth;omega)
  have H:=IntegralMixedMarkedMidpointReceipt.critical hn ht ha hR0 (ROOT old e) i hi labels a b g j hg hw
  unfold IntegralMixedRoadmapSeedMetadata.stageHeader
  exact congrArg (fun c=>(IntegralMixedCommandHeaderBits.command c).context) H

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
