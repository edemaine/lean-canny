/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointFrame
public import LeanCanny.Encoding.IntegralFramedPhysicalCompanionMidpoint
/-! # Every captured MID field is its actual physical coordinate -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProper
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapProper
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "N"=>FormulaSignSlotRadialProviderAtomic.initial
local notation "S"=>FormulaSignSlotRadialProviderAtomic.input

private theorem latest_index (q : List Bool) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    levelIndex q<IntegralMixedRoadmapChain.depth (FormulaSignSlotRadialProviderAtomic.payload q) :=by
  change FormulaSignSlotRadialProviderAtomic.depth q-1<FormulaSignSlotRadialProviderAtomic.depth q
  omega

theorem midpoint_companion_good (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    IntegralMixedChronologicalMidpointCode.Good (D q) (midFirst (D q) (N q) q+i) (labels q)
      (producer false q) (producer true q) (levelIndex q+1) (D q-i) :=by
  have Hlevel:=IntegralMixedRoadmapChain.level_checked (FormulaSignSlotRadialProviderAtomic.checked q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv))
    (levelIndex q) (latest_index q hd)
  have HQ : IntegralMixedRoadmapLevel.freeCount (D q)
      (IntegralMixedRoadmapChain.levelPacket (D q) (FormulaSignSlotRadialProviderAtomic.payload q) (levelIndex q))=captureCount (D q) q :=by
    simp only [IntegralMixedRoadmapLevel.freeCount,IntegralMixedRoadmapLevel.g,
      IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice_k,captureCount]
    omega
  have H:=IntegralMixedRoadmapLevel.checked_midpoint_companion Hlevel i (by rw [HQ];exact hi)
  simpa only [IntegralMixedRoadmapLevel.afterEndpoints,IntegralMixedRoadmapLevel.freshLeft,
    IntegralMixedRoadmapLevel.freshRight,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.producer,IntegralMixedRoadmapLevel.g,
    IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice,
    IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair,IntegralMixedRoadmapChain.frozen_count,
    labels,producer,midFirst,midBirth,baseBirth,IntegralMixedRoadmapChain.freshCount,Nat.add_assoc,
    FormulaSignSlotRadialProviderAtomic.payload,IntegralMixedRoadmapAtomic.payload] using H

theorem midpoint_companion_record (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    WordList.get (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload q)) (midRawIndex (D q) q+1+i)=
      IntegralMixedChronologicalMidpointCode.code (D q) (labels q) (producer false q) (producer true q)
        (levelIndex q+1) (D q-i) :=
  IntegralMixedRoadmapCaptureRecords.checked_mid_record (FormulaSignSlotRadialProviderAtomic.checked q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv))
    (levelIndex q) i (latest_index q hd) hi

theorem midpoint_companion_fit (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    midRawIndex (D q) q+1+i<WordListRecords.count (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload q)) :=by
  have H:=((FormulaSignSlotRadialProviderAtomic.checked q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv)).2.2.2.2.1
    (levelIndex q) (latest_index q hd)).2.2.1
  rw [IntegralMixedRoadmapChain.level_count] at H
  unfold IntegralMixedRoadmapChain.blockCount at H
  unfold midRawIndex
  unfold captureCount at hi
  omega

theorem midpoint_companion_command (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    (IntegralMixedFramedRootPullback.instructionAt (BK).parameters (BK).plan (FormulaSignSlotRadialProviderAtomic.root q)
      (midFirst (D q) (N q) q+i)).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData (D q) (midFirst (D q) (N q) q+i) (labels q)
        (producer false q) (producer true q) (levelIndex q+1) (D q-i)
        (midpoint_companion_good q hv hd i hi)).rule :=by
  have HI : midRawIndex (D q) q+1+i<IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root q):=by
    rw [IntegralMixedCausalRecordPlanBits.count,FormulaSignSlotRadialProviderAtomic.root_records]
    simpa only [FormulaSignSlotRadialProviderAtomic.payload,IntegralMixedRoadmapAtomic.payload]
      using midpoint_companion_fit q hv hd i hi
  have HW : IntegralMixedCausalRecordPlanBits.code (FormulaSignSlotRadialProviderAtomic.root q) (midRawIndex (D q) q+1+i)=
      IntegralMixedChronologicalMidpointCode.code (D q) (labels q) (producer false q) (producer true q)
        (levelIndex q+1) (D q-i):=by
    rw [FormulaSignSlotRadialProviderAtomic.root_record_code]
    exact midpoint_companion_record q hv hd i hi
  have HB : midFirst (D q) (N q) q+i=FormulaSignSlotRadialProviderRecordPlan.count
      (FormulaSignSlotRadialProviderAtomic.root q)+(midRawIndex (D q) q+1+i):=by
    have HN : FormulaSignSlotRadialProviderRecordPlan.count (FormulaSignSlotRadialProviderAtomic.root q)=N q:=rfl
    rw [HN]
    simp only [midFirst,midBirth,baseBirth,IntegralMixedRoadmapChain.birth,midRawIndex,
      FormulaSignSlotRadialProviderAtomic.payload,IntegralMixedRoadmapAtomic.payload]
    omega
  exact midpoint_record_at (FormulaSignSlotRadialProviderAtomic.root q) (midRawIndex (D q) q+1+i)
    (midFirst (D q) (N q) q+i) HI HB (labels q) (producer false q) (producer true q)
    (levelIndex q+1) (D q-i) (midpoint_companion_good q hv hd i hi) HW



theorem midpoint_companion_context_good (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    IntegralMixedChronologicalMidpointCode.Good ((BK).parameters.ambient (pairFst ((BK).key (FormulaSignSlotRadialProviderAtomic.context q))))
      (midFirst (D q) (N q) q+i) (labels q) (producer false q) (producer true q) (levelIndex q+1) (D q-i) :=by
  rw [FormulaSignSlotRadialProviderAtomic.context_root q]
  exact midpoint_companion_good q hv hd i hi

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

theorem midpoint_companion_context_command (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    (IntegralMixedFramedRootPullback.instructionAt (BK).parameters (BK).plan
      (pairFst ((BK).key (FormulaSignSlotRadialProviderAtomic.context q))) (midFirst (D q) (N q) q+i)).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData
        ((BK).parameters.ambient (pairFst ((BK).key (FormulaSignSlotRadialProviderAtomic.context q))))
        (midFirst (D q) (N q) q+i) (labels q) (producer false q) (producer true q) (levelIndex q+1) (D q-i)
        (midpoint_companion_context_good q hv hd i hi)).rule :=by
  exact capture_root_transport (BK).parameters (BK).plan (FormulaSignSlotRadialProviderAtomic.root q)
    (pairFst ((BK).key (FormulaSignSlotRadialProviderAtomic.context q)))
    (FormulaSignSlotRadialProviderAtomic.context_root q).symm _ _ _ _ _ _
    (midpoint_companion_good q hv hd i hi) (midpoint_companion_context_good q hv hd i hi)
    (midpoint_companion_command q hv hd i hi)

theorem midpoint_capture_selected (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    IntegralFramedPhysicalCompanionPoint.selected BK FormulaSignSlotRadialProviderRecordPlan.tables
      (FormulaSignSlotRadialProviderAtomic.context q) (midFirst (D q) (N q) q+i)=D q-i :=
  IntegralFramedPhysicalCompanionPoint.selected_of_midpoint BK FormulaSignSlotRadialProviderRecordPlan.tables FormulaSignSlotRadialProviderAtomic.bank_represents
    (FormulaSignSlotRadialProviderAtomic.context q) (midFirst (D q) (N q) q+i) (labels q)
    (producer false q) (producer true q) (levelIndex q+1) (D q-i)
    (midpoint_companion_context_good q hv hd i hi) (midpoint_companion_context_command q hv hd i hi)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProper
