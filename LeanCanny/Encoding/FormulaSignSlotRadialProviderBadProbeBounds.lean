/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeCommand
/-! # Checked bad hints derive all actual interval packet bounds -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeBounds
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "dim" => FormulaSignSlotRadialProviderBadProbeTest.dimension
local notation "ini" => FormulaSignSlotRadialProviderBadProbeTest.initial
local notation "wid" => FormulaSignSlotRadialProviderBadProbeTest.width
local notation "ctx" => FormulaSignSlotRadialProviderBadProbeTest.intervalContext

private theorem guard_parent (p : Parameters) (q w : List Bool) :
    IntegralFramedTraceCutGuards.parent p (FormulaSignSlotRadialProviderCutInterval.guardPacket (pair q w))=
      IntegralFramedTraceCutTask.task p (pair (pairFst q) (pair (FormulaSignSlotRadialProviderCutInterval.birthWord q) [])) := by
  simp only [IntegralFramedTraceCutGuards.parent,Function.comp_apply,IntegralFramedTraceCutGuards.descriptor,
    IntegralFramedTraceCutGuards.root,FormulaSignSlotRadialProviderCutInterval.guardPacket,pairFst_pair,pairSnd_pair]

theorem selected (side : Bool) (z : List Bool) :
    FormulaSignSlotRadialProviderCutInterval.selected side (ctx z)=
      FormulaSignSlotRadialProviderBadProbeProvenance.birth z-
        IntegralMixedRoadmapBadProbePacket.producer side (pairFst z) := by
  cases side <;> simp only [FormulaSignSlotRadialProviderCutInterval.selected,
    FormulaSignSlotRadialProviderBadProbeTest.intervalContext,IntegralMixedRoadmapBadProbePacket.intervalContext,
    FormulaSignSlotRadialProviderBadProbeProvenance.birth,IntegralMixedRoadmapBadProbePacket.producer,
    Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderAtomic.Cuts.StageCut IntegralFramedCreatingCut.ParentCut

variable (z : List Bool) (hh : IntegralMixedRoadmapBadProbePacket.HintGood (dim z) (ini z) (wid z) z)

include hh in
theorem count : FormulaSignSlotRadialProviderCutInterval.count (ctx z)=
    FormulaSignSlotRadialProviderBadProbeProvenance.birth z+1 :=
  (FormulaSignSlotRadialProviderCutInterval.count_eq (ctx z)).trans
    ((congrArg FormulaSignSlotRadialProviderRecordPlan.fullCount
      (FormulaSignSlotRadialProviderBadProbeProvenance.context_root z)).trans
        (FormulaSignSlotRadialProviderBadProbeProvenance.last_birth z hh).symm)

include hh in
theorem stage_cut (w : List Bool) : FormulaSignSlotRadialProviderAtomic.Cuts.StageCut
    (FormulaSignSlotRadialProviderCutInterval.guardPacket (pair (ctx z) w)) := by
  have HP : IntegralFramedTraceCutGuards.parent P
      (FormulaSignSlotRadialProviderCutInterval.guardPacket (pair (ctx z) w))=
        FormulaSignSlotRadialProviderCutInterval.parent (ctx z) := guard_parent P (ctx z) w
  have HC := FormulaSignSlotRadialProviderBadProbeCommand.interval_parent_cut z hh
  unfold FormulaSignSlotRadialProviderAtomic.Cuts.StageCut IntegralFramedTraceCutScan.StageCut
  change IntegralFramedCreatingCut.ParentCut P D (IntegralFramedTraceCutGuards.parent P _)
  exact (congrArg (IntegralFramedCreatingCut.ParentCut P D) HP).mpr HC

include hh in
theorem bounds (w : List Bool) : FormulaSignSlotRadialProviderCutInterval.Bounds (pair (ctx z) w) := by
  unfold FormulaSignSlotRadialProviderCutInterval.Bounds
  simp only [pairFst_pair]
  refine ⟨?_,?_,?_,stage_cut z hh w⟩
  · rw [selected,count z hh]
    omega
  · rw [selected,count z hh]
    omega
  · rw [FormulaSignSlotRadialProviderBadProbeProvenance.context_birth,count z hh]
    omega

attribute [local irreducible] FormulaSignSlotRadialProviderBadProbeTest.Witness

theorem witness_iff (z w : List Bool) :
    FormulaSignSlotRadialProviderBadProbeTest.Witness (pair z w) ↔
      IntegralMixedRoadmapBadProbePacket.HintGood (dim z) (ini z) (wid z) z ∧
      FormulaSignSlotRadialProviderBadProbeTest.fieldPacket (pair z w)∈FormulaSignSlotRadialProviderFieldEqualityList.language ∧
      SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (ctx z) w ∧
      FormulaSignSlotRadialProviderCutInterval.Guards (FormulaSignSlotRadialProviderBadProbeTest.intervalPacket (pair z w)) ∧
      FormulaSignSlotRadialProviderBadProbeTest.intervalPacket (pair z w)∉FormulaSignSlotRadialProviderCutInterval.language := by
  unfold FormulaSignSlotRadialProviderBadProbeTest.Witness
  simp only [pairFst_pair,pairSnd_pair]
  constructor
  · intro h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩
  · rintro ⟨hh,hf,hv,hg,hn⟩
    have hb : FormulaSignSlotRadialProviderCutInterval.Bounds
        (FormulaSignSlotRadialProviderBadProbeTest.intervalPacket (pair z w)) := by
      simpa only [FormulaSignSlotRadialProviderBadProbeTest.intervalPacket,pairFst_pair,pairSnd_pair] using bounds z hh w
    exact ⟨hh,hf,hv,hb,hg,hn⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeBounds
