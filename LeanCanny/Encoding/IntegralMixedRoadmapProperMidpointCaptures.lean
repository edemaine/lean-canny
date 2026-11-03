/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidpointFrame
/-! # Every captured MID field is its actual physical coordinate -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProper
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false

private theorem latest_index (q : List Bool) (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    levelIndex q<IntegralMixedRoadmapChain.depth (IntegralMixedRoadmapAtomic.payload q) :=by
  change IntegralMixedRoadmapAtomic.depth q-1<IntegralMixedRoadmapAtomic.depth q
  omega

theorem midpoint_companion_good (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    IntegralMixedChronologicalMidpointCode.Good (D q) (midFirst (D q) (N q) q+i) (labels q)
      (producer false q) (producer true q) (levelIndex q+1) (D q-i) :=by
  have Hlevel:=IntegralMixedRoadmapChain.level_checked (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 q hv)
    (levelIndex q) (latest_index q hd)
  have HQ : IntegralMixedRoadmapLevel.freeCount (D q)
      (IntegralMixedRoadmapChain.levelPacket (D q) (IntegralMixedRoadmapAtomic.payload q) (levelIndex q))=captureCount (D q) q :=by
    simp only [IntegralMixedRoadmapLevel.freeCount,IntegralMixedRoadmapLevel.g,
      IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice_k,captureCount]
    omega
  have H:=IntegralMixedRoadmapLevel.checked_midpoint_companion Hlevel i (by rw [HQ];exact hi)
  simpa only [IntegralMixedRoadmapLevel.afterEndpoints,IntegralMixedRoadmapLevel.freshLeft,
    IntegralMixedRoadmapLevel.freshRight,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.producer,IntegralMixedRoadmapLevel.g,
    IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice,
    IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair,IntegralMixedRoadmapChain.frozen_count,
    labels,producer,midFirst,midBirth,baseBirth,IntegralMixedRoadmapChain.freshCount,Nat.add_assoc] using H

theorem midpoint_companion_record (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) (midRawIndex (D q) q+1+i)=
      IntegralMixedChronologicalMidpointCode.code (D q) (labels q) (producer false q) (producer true q)
        (levelIndex q+1) (D q-i) :=
  IntegralMixedRoadmapCaptureRecords.checked_mid_record (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 q hv)
    (levelIndex q) i (latest_index q hd) hi

theorem midpoint_companion_fit (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    midRawIndex (D q) q+1+i<WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) :=by
  have H:=((IntegralMixedRoadmapAtomic.checked hn ht ha hR0 q hv).2.2.2.2.1
    (levelIndex q) (latest_index q hd)).2.2.1
  rw [IntegralMixedRoadmapChain.level_count] at H
  unfold IntegralMixedRoadmapChain.blockCount at H
  unfold midRawIndex
  unfold captureCount at hi
  omega

theorem midpoint_companion_command (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    (IntegralMixedFramedRootPullback.instructionAt (BK).parameters (BK).plan (IntegralMixedRoadmapAtomic.root q)
      (midFirst (D q) (N q) q+i)).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData (D q) (midFirst (D q) (N q) q+i) (labels q)
        (producer false q) (producer true q) (levelIndex q+1) (D q-i)
        (midpoint_companion_good hn ht ha hR0 q hv hd i hi)).rule :=by
  have HI : midRawIndex (D q) q+1+i<IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q):=by
    simpa only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
      IntegralMixedRoadmapAtomic.root,pairFst_pair,pairSnd_pair] using midpoint_companion_fit hn ht ha hR0 q hv hd i hi
  have HW : IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root q) (midRawIndex (D q) q+1+i)=
      IntegralMixedChronologicalMidpointCode.code (D q) (labels q) (producer false q) (producer true q)
        (levelIndex q+1) (D q-i):=by
    simpa only [IntegralMixedCausalRecordPlanBits.code,IntegralMixedCausalRecordPlanBits.records,
      IntegralMixedRoadmapAtomic.root,pairFst_pair,pairSnd_pair] using midpoint_companion_record hn ht ha hR0 q hv hd i hi
  have HN : IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapAtomic.root q)+8=N q:=by
    rw [IntegralMixedRoadmapAtomic.initial_eq hn ht ha hR0 q]
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,pairFst_pair,
      IntegralMixedRoadmapAtomic.original]
  have HB : midFirst (D q) (N q) q+i=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapAtomic.root q)+8+(midRawIndex (D q) q+1+i):=by
    unfold midFirst midBirth baseBirth IntegralMixedRoadmapChain.birth midRawIndex
    rw [HN]
    omega
  exact IntegralMixedMarkedMidpointReceipt.critical_at hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q)
    (midRawIndex (D q) q+1+i) (midFirst (D q) (N q) q+i) HI HB (labels q) (producer false q) (producer true q)
    (levelIndex q+1) (D q-i) (midpoint_companion_good hn ht ha hR0 q hv hd i hi) HW


theorem midpoint_companion_context_good (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    IntegralMixedChronologicalMidpointCode.Good ((BK).parameters.ambient (pairFst ((BK).key (IntegralMixedRoadmapAtomic.context q))))
      (midFirst (D q) (N q) q+i) (labels q) (producer false q) (producer true q) (levelIndex q+1) (D q-i) :=by
  rw [IntegralMixedRoadmapAtomic.context_root hn ht ha hR0 q]
  exact midpoint_companion_good hn ht ha hR0 q hv hd i hi

private theorem capture_root_transport (P : IntegralCriticalHistoryTask.Parameters)
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

theorem midpoint_companion_context_command (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    (IntegralMixedFramedRootPullback.instructionAt (BK).parameters (BK).plan
      (pairFst ((BK).key (IntegralMixedRoadmapAtomic.context q))) (midFirst (D q) (N q) q+i)).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData
        ((BK).parameters.ambient (pairFst ((BK).key (IntegralMixedRoadmapAtomic.context q))))
        (midFirst (D q) (N q) q+i) (labels q) (producer false q) (producer true q) (levelIndex q+1) (D q-i)
        (midpoint_companion_context_good hn ht ha hR0 q hv hd i hi)).rule :=by
  exact capture_root_transport (BK).parameters (BK).plan (IntegralMixedRoadmapAtomic.root q)
    (pairFst ((BK).key (IntegralMixedRoadmapAtomic.context q)))
    (IntegralMixedRoadmapAtomic.context_root hn ht ha hR0 q).symm _ _ _ _ _ _
    (midpoint_companion_good hn ht ha hR0 q hv hd i hi) (midpoint_companion_context_good hn ht ha hR0 q hv hd i hi)
    (midpoint_companion_command hn ht ha hR0 q hv hd i hi)

theorem midpoint_capture_selected (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (midFirst (D q) (N q) q+i)=D q-i :=
  IntegralMixedPhysicalPointCompanionScan.selected_of_midpoint hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context q) (midFirst (D q) (N q) q+i) (labels q)
    (producer false q) (producer true q) (levelIndex q+1) (D q-i)
    (midpoint_companion_context_good hn ht ha hR0 q hv hd i hi) (midpoint_companion_context_command hn ht ha hR0 q hv hd i hi)

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalPointCompanionScan.retained
  IntegralMixedPhysicalPointCompanionScan.selected

theorem midpoint_capture_readback (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (HM : Midpoint hn ht ha hR0 q)
    (i : ℕ) (hi : i<captureCount (D q) q) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (midFirst (D q) (N q) q+i)=
    IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (midBirth (D q) (N q) q)
      ⟨D q-i,by rw [IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q];omega⟩ :=by
  obtain ⟨hvM,_,HC⟩:=midpoint_sound hn ht ha hR0 q HM
  obtain ⟨hb,_,HR⟩:=HC i hi
  have HE:=IntegralMixedPhysicalFieldEquality.retained_point hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hvM (midFirst (D q) (N q) q+i) hb
  have HF : (⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (midFirst (D q) (N q) q+i),
      IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩ :
      Fin ((BK).parameters.ambient (pairFst ((BK).key (IntegralMixedRoadmapAtomic.context q)))+1))=
      ⟨D q-i,by rw [IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q];omega⟩ :=
    Fin.ext (midpoint_capture_selected hn ht ha hR0 q hv hd i hi)
  rw [HF] at HR
  exact HE.symm.trans HR

end LeanCanny.Encoding.IntegralMixedRoadmapProper
