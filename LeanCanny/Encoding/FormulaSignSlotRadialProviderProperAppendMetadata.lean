/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendHeader
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedNoCut
/-! # All proper stages after MID are critical, including the seed tail -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open FormulaSignSlotRadialProviderRecordPrefix (context)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderIntegerSource.source preparedRoot start
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial

variable (old : List Bool) (hv : A old) (hd : depth old<dimension old)
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side

include hv hd in
theorem seed_code_after_finish (b : ℕ) (hb0 : finishBirth old hv hd left right R side≤b) (hb1 : b<fullBirth old hv hd left right R side) :
    IntegralMixedCausalRecordPlanBits.code r (b-N old)=
      IntegralMixedChronologicalFrameCode.code ((P).ambient r) [] 0 0 := by
  have HR := prepared_seed_records old hv hd left right R side
  have HC : IntegralMixedCausalRecordPlanBits.count r=
      (meaningfulCodes old hv hd left right R side).length+tailCount old hv hd left right R side := by
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [HR,WordListRecords.count_encode,List.length_append,List.length_replicate]
  have HF := meaningful_finish old hv hd left right R side
  rw [prepared_initial] at HF
  have HB : b<N old+IntegralMixedCausalRecordPlanBits.count r := by
    change b<FormulaSignSlotRadialProviderRecordPlan.count r+_ at hb1
    rw [prepared_initial] at hb1
    exact hb1
  have HI : b-N old-(meaningfulCodes old hv hd left right R side).length<tailCount old hv hd left right R side := by omega
  rw [IntegralMixedCausalRecordPlanBits.code,HR,WordList.get_encode,
    List.getElem?_append_right (by omega)]
  simp only [List.getElem?_replicate,HI,ite_true,Option.getD_some]

include hv hd in
theorem seed_metadata_after_finish (b : ℕ) (hb0 : finishBirth old hv hd left right R side≤b) (hb1 : b<fullBirth old hv hd left right R side) :
    FormulaSignSlotRadialProviderAtomic.Active (context r) b ∧
      FormulaSignSlotRadialProviderAtomic.selected (context r) b=0 := by
  have HF := finish_eq old hv hd left right R side
  have HN : N old≤midpointBirth old hv hd left right R := by
    unfold midpointBirth
    rw [begin_eq_start]
    omega
  have HB0 : N old≤b := by omega
  let i := b-N old
  have HB : b=FormulaSignSlotRadialProviderRecordPlan.count r+i := by
    rw [prepared_initial]
    dsimp only [i]
    omega
  have HI : i<IntegralMixedCausalRecordPlanBits.count r := by
    change b<FormulaSignSlotRadialProviderRecordPlan.count r+_ at hb1
    rw [prepared_initial] at hb1
    dsimp only [i]
    omega
  have HG := IntegralMixedRoadmapChain.seed_point_good ((P).ambient r)
    (FormulaSignSlotRadialProviderRecordPlan.count r+i) 0 (Nat.zero_lt_succ _)
  have H := FormulaSignSlotRadialProviderRecordCriticalMetadata.frame_metadata r i HI [] 0 0 HG
    (seed_code_after_finish old hv hd left right R side b hb0 hb1)
  exact ⟨Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context r) b) HB.symm) H.1,
    (congrArg (FormulaSignSlotRadialProviderAtomic.selected (context r)) HB).trans H.2⟩

include hv hd in
theorem active_after_midpoint (b : ℕ) (hb0 : midpointBirth old hv hd left right R≤b) (hb1 : b<fullBirth old hv hd left right R side) :
    FormulaSignSlotRadialProviderAtomic.Active (context r) b := by
  by_cases HT : finishBirth old hv hd left right R side≤b
  · exact (seed_metadata_after_finish old hv hd left right R side b HT hb1).1
  have HF := finish_eq old hv hd left right R side
  let a := midpointBirth old hv hd left right R
  let k := dimension old-depth old
  by_cases HM : b=a
  · have H := (midpoint_anchor_metadata old hv hd left right R side).1
    exact Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context r) b) HM.symm) H
  by_cases HMC : b<a+1+k
  · let i := b-(a+1)
    have HI : i<dimension old-depth old := by dsimp only [i,a,k] at *;omega
    have H := (midpoint_capture_metadata old hv hd left right R side i HI).1
    have HE : midpointBirth old hv hd left right R+1+i=b := by dsimp only [i,a] at *;omega
    exact Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context r) b) HE) H
  by_cases HC : b=a+1+k
  · have H := (child_anchor_metadata old hv hd left right R side).1
    exact Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context r) b) HC.symm) H
  · let i := b-(a+2+k)
    have HI : i<dimension old-depth old := by dsimp only [i,a,k] at *;omega
    have H := (child_capture_metadata old hv hd left right R side i HI).1
    have HE : midpointBirth old hv hd left right R+2+(dimension old-depth old)+i=b := by dsimp only [i,a,k] at *;omega
    exact Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context r) b) HE) H

attribute [local irreducible] FormulaSignSlotRadialProviderFirstSeed.CutFreeAt
  IntegralFramedCreatingCut.IsCut IntegralMixedFramedRootPullback.instructionAt

include hv hd in
theorem no_cut_after_midpoint (b : ℕ) (hb0 : midpointBirth old hv hd left right R≤b) (hb1 : b<fullBirth old hv hd left right R side) :
    FormulaSignSlotRadialProviderFirstSeed.CutFreeAt P D r b := by
  have HA := active_after_midpoint old hv hd left right R side b hb0 hb1
  have HH : (FormulaSignSlotRadialProviderRecordPrefix.header r b).context=1 := HA.2
  rw [FormulaSignSlotRadialProviderRecordPrefix.header_actual] at HH
  unfold FormulaSignSlotRadialProviderFirstSeed.CutFreeAt
  intro HC
  have HE := (IntegralFramedCreatingCut.isCut_iff_context _).mp HC
  rw [←IntegralMixedCommandHeaderBits.command_context,HH] at HE
  omega

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
