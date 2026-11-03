/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicSignature
public import LeanCanny.Encoding.IntegralMixedRoadmapProperBaseReadback
public import LeanCanny.Encoding.IntegralMixedRoadmapMidpointRecord
public import LeanCanny.Encoding.IntegralMixedMarkedMidpointReceipt
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalMidpoint
/-! # A checked proper midpoint has its actual creating midpoint command -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProper
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0

private theorem latest_lt (q : List Bool) (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    levelIndex q<IntegralMixedRoadmapChain.depth (IntegralMixedRoadmapAtomic.payload q) :=by
  change IntegralMixedRoadmapAtomic.depth q-1<IntegralMixedRoadmapAtomic.depth q
  omega

theorem midpoint_good (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    IntegralMixedChronologicalMidpointCode.Good (D q) (midBirth (D q) (N q) q) (labels q)
      (producer false q) (producer true q) (levelIndex q+1) (levelIndex q+1) :=by
  have H:=IntegralMixedRoadmapLevel.checked_midpoint_anchor
    (IntegralMixedRoadmapChain.level_checked (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 q hv)
      (levelIndex q) (latest_lt q hd))
  simpa only [IntegralMixedRoadmapLevel.afterEndpoints,IntegralMixedRoadmapLevel.freshLeft,
    IntegralMixedRoadmapLevel.freshRight,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.producer,IntegralMixedRoadmapLevel.g,
    IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice,
    IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair,IntegralMixedRoadmapChain.frozen_count,
    labels,producer,midBirth,baseBirth,IntegralMixedRoadmapChain.freshCount,Nat.add_assoc] using H

def midRawIndex (dimension : ℕ) (q : List Bool):=
  IntegralMixedRoadmapChain.rawStart dimension (IntegralMixedRoadmapAtomic.payload q) (levelIndex q)+
    IntegralMixedRoadmapChain.freshCount (IntegralMixedRoadmapAtomic.payload q) (levelIndex q)

theorem midpoint_record (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) (midRawIndex (D q) q)=
      IntegralMixedChronologicalMidpointCode.code (D q) (labels q) (producer false q) (producer true q)
        (levelIndex q+1) (levelIndex q+1) :=
  IntegralMixedRoadmapMidpointRecord.checked_anchor_record (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 q hv)
    (levelIndex q) (latest_lt q hd)

theorem midpoint_fit (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    midRawIndex (D q) q<WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) :=by
  have H:=((IntegralMixedRoadmapAtomic.checked hn ht ha hR0 q hv).2.2.2.2.1
    (levelIndex q) (latest_lt q hd)).2.2.1
  rw [IntegralMixedRoadmapChain.level_count] at H
  unfold IntegralMixedRoadmapChain.blockCount at H
  unfold midRawIndex
  omega

theorem midpoint_command (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    (IntegralMixedFramedRootPullback.instructionAt (B).parameters (B).plan (IntegralMixedRoadmapAtomic.root q)
      (midBirth (D q) (N q) q)).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData (D q) (midBirth (D q) (N q) q) (labels q)
        (producer false q) (producer true q) (levelIndex q+1) (levelIndex q+1) (midpoint_good hn ht ha hR0 q hv hd)).rule :=by
  have HI : midRawIndex (D q) q<IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q):=by
    simpa only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
      IntegralMixedRoadmapAtomic.root,pairFst_pair,pairSnd_pair] using midpoint_fit hn ht ha hR0 q hv hd
  have HW : IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root q) (midRawIndex (D q) q)=
      IntegralMixedChronologicalMidpointCode.code (D q) (labels q) (producer false q) (producer true q)
        (levelIndex q+1) (levelIndex q+1):=by
    simpa only [IntegralMixedCausalRecordPlanBits.code,IntegralMixedCausalRecordPlanBits.records,
      IntegralMixedRoadmapAtomic.root,pairFst_pair,pairSnd_pair] using midpoint_record hn ht ha hR0 q hv hd
  have HN : IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapAtomic.root q)+8=N q:=by
    rw [IntegralMixedRoadmapAtomic.initial_eq hn ht ha hR0 q]
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,pairFst_pair,
      IntegralMixedRoadmapAtomic.original]
  have HB : midBirth (D q) (N q) q=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapAtomic.root q)+8+midRawIndex (D q) q:=by
    unfold midBirth baseBirth IntegralMixedRoadmapChain.birth midRawIndex
    rw [HN]
    omega
  exact IntegralMixedMarkedMidpointReceipt.critical_at hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q)
    (midRawIndex (D q) q) (midBirth (D q) (N q) q) HI HB (labels q) (producer false q) (producer true q)
    (levelIndex q+1) (levelIndex q+1) (midpoint_good hn ht ha hR0 q hv hd) HW


theorem midpoint_context_good (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    IntegralMixedChronologicalMidpointCode.Good ((B).parameters.ambient (pairFst ((B).key (IntegralMixedRoadmapAtomic.context q))))
      (midBirth (D q) (N q) q) (labels q) (producer false q) (producer true q) (levelIndex q+1) (levelIndex q+1) :=by
  rw [IntegralMixedRoadmapAtomic.context_root hn ht ha hR0 q]
  exact midpoint_good hn ht ha hR0 q hv hd

private theorem midpoint_root_transport (P : IntegralCriticalHistoryTask.Parameters)
    (plan0 : IntegralMixedFramedHistoryFamilyBits.Plan P) (r s : List Bool) (he : r=s)
    (birth : ℕ) (labels : List Bool) (a b g j : ℕ)
    (HG : IntegralMixedChronologicalMidpointCode.Good (P.ambient r) birth labels a b g j)
    (HS : IntegralMixedChronologicalMidpointCode.Good (P.ambient s) birth labels a b g j)
    (hc : (IntegralMixedFramedRootPullback.instructionAt P plan0 r birth).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData (P.ambient r) birth labels a b g j HG).rule) :
    (IntegralMixedFramedRootPullback.instructionAt P plan0 s birth).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData (P.ambient s) birth labels a b g j HS).rule :=by
  subst s
  exact hc

theorem midpoint_context_command (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    (IntegralMixedFramedRootPullback.instructionAt (B).parameters (B).plan
      (pairFst ((B).key (IntegralMixedRoadmapAtomic.context q))) (midBirth (D q) (N q) q)).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData
        ((B).parameters.ambient (pairFst ((B).key (IntegralMixedRoadmapAtomic.context q))))
        (midBirth (D q) (N q) q) (labels q) (producer false q) (producer true q) (levelIndex q+1) (levelIndex q+1)
        (midpoint_context_good hn ht ha hR0 q hv hd)).rule :=by
  exact midpoint_root_transport (B).parameters (B).plan (IntegralMixedRoadmapAtomic.root q)
    (pairFst ((B).key (IntegralMixedRoadmapAtomic.context q)))
    (IntegralMixedRoadmapAtomic.context_root hn ht ha hR0 q).symm _ _ _ _ _ _
    (midpoint_good hn ht ha hR0 q hv hd) (midpoint_context_good hn ht ha hR0 q hv hd)
    (midpoint_command hn ht ha hR0 q hv hd)

end LeanCanny.Encoding.IntegralMixedRoadmapProper
