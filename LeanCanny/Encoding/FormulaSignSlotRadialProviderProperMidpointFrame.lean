/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicSignature
public import LeanCanny.Encoding.IntegralMixedRoadmapProperLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordReceipt
public import LeanCanny.Algebra.IntegralMixedStaticMidpointReceipt
public import LeanCanny.Encoding.IntegralMixedRoadmapMidpointRecord
/-! # A checked proper midpoint has its actual creating midpoint command -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProper
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapProper
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "N"=>FormulaSignSlotRadialProviderAtomic.initial
attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderRecordPlan.spatial

theorem midpoint_record_at (root : List Bool) (i birth : ℕ)
    (hi : i<IntegralMixedCausalRecordPlanBits.count root)
    (hb : birth=FormulaSignSlotRadialProviderRecordPlan.count root+i)
    (labels : List Bool) (a b g j : ℕ)
    (hg : IntegralMixedChronologicalMidpointCode.Good ((B).parameters.ambient root) birth labels a b g j)
    (hw : IntegralMixedCausalRecordPlanBits.code root i=IntegralMixedChronologicalMidpointCode.code
      ((B).parameters.ambient root) labels a b g j) :
    (IntegralMixedFramedRootPullback.instructionAt (B).parameters (B).plan root birth).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData ((B).parameters.ambient root)
        birth labels a b g j hg).rule :=by
  subst birth
  dsimp only [FormulaSignSlotRadialProviderRecordPlan.bank] at *
  have HR : IntegralMixedCausalRecordPlanBits.count root+FormulaSignSlotRadialProviderRecordPlan.count root≤
      (B).parameters.cap root+1+1:=by
    have HH:=FormulaSignSlotRadialProviderRecordReceipt.room root
    rw [FormulaSignSlotRadialProviderRecordReceipt.records_length] at HH
    exact HH
  unfold IntegralMixedFramedRootPullback.instructionAt
  rw [FormulaSignSlotRadialProviderRecordReceipt.rules]
  unfold FormulaSignSlotRadialProviderRecordReceipt.records
  exact IntegralMixedStaticRecordLookup.midpoint_receipt
    (FormulaSignSlotRadialProviderRecordPlan.spatial root)
    (FormulaSignSlotRadialProviderRecordPlan.positive root)
    (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap root)
    (FormulaSignSlotRadialProviderRecordPlan.count root) (IntegralMixedCausalRecordPlanBits.count root)
    (FormulaSignSlotRadialProviderRecordReceipt.polynomial root)
    (FormulaSignSlotRadialProviderRecordReceipt.polynomial_nonzero root)
    (FormulaSignSlotRadialProviderRecordReceipt.polynomial_degree root)
    (IntegralMixedCausalRecordPlanBits.code root)
    (IntegralMixedFramedHistoryFamilyBits.initial (B).parameters (B).plan root) HR
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction (B).parameters (B).plan root)
    i hi labels a b g j hg hw

private theorem latest_lt (q : List Bool) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    levelIndex q<IntegralMixedRoadmapChain.depth (FormulaSignSlotRadialProviderAtomic.payload q) :=by
  change FormulaSignSlotRadialProviderAtomic.depth q-1<FormulaSignSlotRadialProviderAtomic.depth q
  omega

theorem midpoint_good (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    IntegralMixedChronologicalMidpointCode.Good (D q) (midBirth (D q) (N q) q) (labels q)
      (producer false q) (producer true q) (levelIndex q+1) (levelIndex q+1) :=by
  have H:=IntegralMixedRoadmapLevel.checked_midpoint_anchor
    (IntegralMixedRoadmapChain.level_checked (FormulaSignSlotRadialProviderAtomic.checked q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv))
      (levelIndex q) (latest_lt q hd))
  simpa only [IntegralMixedRoadmapLevel.afterEndpoints,IntegralMixedRoadmapLevel.freshLeft,
    IntegralMixedRoadmapLevel.freshRight,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.producer,IntegralMixedRoadmapLevel.g,
    IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice,
    IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair,IntegralMixedRoadmapChain.frozen_count,
    labels,producer,midBirth,baseBirth,IntegralMixedRoadmapChain.freshCount,Nat.add_assoc,
    FormulaSignSlotRadialProviderAtomic.payload,IntegralMixedRoadmapAtomic.payload] using H

def midRawIndex (dimension : ℕ) (q : List Bool):=
  IntegralMixedRoadmapChain.rawStart dimension (FormulaSignSlotRadialProviderAtomic.payload q) (levelIndex q)+
    IntegralMixedRoadmapChain.freshCount (FormulaSignSlotRadialProviderAtomic.payload q) (levelIndex q)

theorem midpoint_record (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    WordList.get (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload q)) (midRawIndex (D q) q)=
      IntegralMixedChronologicalMidpointCode.code (D q) (labels q) (producer false q) (producer true q)
        (levelIndex q+1) (levelIndex q+1) :=
  IntegralMixedRoadmapMidpointRecord.checked_anchor_record (FormulaSignSlotRadialProviderAtomic.checked q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv))
    (levelIndex q) (latest_lt q hd)

theorem midpoint_fit (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    midRawIndex (D q) q<WordListRecords.count (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload q)) :=by
  have H:=((FormulaSignSlotRadialProviderAtomic.checked q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv)).2.2.2.2.1
    (levelIndex q) (latest_lt q hd)).2.2.1
  rw [IntegralMixedRoadmapChain.level_count] at H
  unfold IntegralMixedRoadmapChain.blockCount at H
  unfold midRawIndex
  omega

theorem midpoint_command (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    (IntegralMixedFramedRootPullback.instructionAt (B).parameters (B).plan (FormulaSignSlotRadialProviderAtomic.root q)
      (midBirth (D q) (N q) q)).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData (D q) (midBirth (D q) (N q) q) (labels q)
        (producer false q) (producer true q) (levelIndex q+1) (levelIndex q+1) (midpoint_good q hv hd)).rule :=by
  have HI : midRawIndex (D q) q<IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root q):=by
    rw [IntegralMixedCausalRecordPlanBits.count,FormulaSignSlotRadialProviderAtomic.root_records]
    simpa only [FormulaSignSlotRadialProviderAtomic.payload,IntegralMixedRoadmapAtomic.payload]
      using midpoint_fit q hv hd
  have HW : IntegralMixedCausalRecordPlanBits.code (FormulaSignSlotRadialProviderAtomic.root q) (midRawIndex (D q) q)=
      IntegralMixedChronologicalMidpointCode.code (D q) (labels q) (producer false q) (producer true q)
        (levelIndex q+1) (levelIndex q+1):=by
    rw [FormulaSignSlotRadialProviderAtomic.root_record_code]
    exact midpoint_record q hv hd
  have HB : midBirth (D q) (N q) q=FormulaSignSlotRadialProviderRecordPlan.count
      (FormulaSignSlotRadialProviderAtomic.root q)+midRawIndex (D q) q:=by
    have HN : FormulaSignSlotRadialProviderRecordPlan.count (FormulaSignSlotRadialProviderAtomic.root q)=N q:=by
      unfold FormulaSignSlotRadialProviderAtomic.initial
      rfl
    rw [HN]
    simp only [midBirth,baseBirth,IntegralMixedRoadmapChain.birth,midRawIndex,
      FormulaSignSlotRadialProviderAtomic.payload,IntegralMixedRoadmapAtomic.payload]
    omega
  exact midpoint_record_at (FormulaSignSlotRadialProviderAtomic.root q) (midRawIndex (D q) q)
    (midBirth (D q) (N q) q) HI HB (labels q) (producer false q) (producer true q)
    (levelIndex q+1) (levelIndex q+1) (midpoint_good q hv hd) HW



theorem midpoint_context_good (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    IntegralMixedChronologicalMidpointCode.Good ((B).parameters.ambient (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context q))))
      (midBirth (D q) (N q) q) (labels q) (producer false q) (producer true q) (levelIndex q+1) (levelIndex q+1) :=by
  rw [FormulaSignSlotRadialProviderAtomic.context_root q]
  exact midpoint_good q hv hd

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

theorem midpoint_context_command (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    (IntegralMixedFramedRootPullback.instructionAt (B).parameters (B).plan
      (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context q))) (midBirth (D q) (N q) q)).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData
        ((B).parameters.ambient (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context q))))
        (midBirth (D q) (N q) q) (labels q) (producer false q) (producer true q) (levelIndex q+1) (levelIndex q+1)
        (midpoint_context_good q hv hd)).rule :=by
  exact midpoint_root_transport (B).parameters (B).plan (FormulaSignSlotRadialProviderAtomic.root q)
    (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context q)))
    (FormulaSignSlotRadialProviderAtomic.context_root q).symm _ _ _ _ _ _
    (midpoint_good q hv hd) (midpoint_context_good q hv hd)
    (midpoint_command q hv hd)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProper
