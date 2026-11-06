/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendHeader
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedNoCut
/-! # Every new retained-extension stage is critical, including its seed tail -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
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
  (e : ℕ) (he : e<endBirth (dimension old) (N old) old)

include hv hd he in
theorem seed_code_after_finish (b : ℕ) (hb0 : finishBirth old e≤b) (hb1 : b<fullBirth old e) :
    IntegralMixedCausalRecordPlanBits.code (preparedRoot old e) (b-N old)=
      IntegralMixedChronologicalFrameCode.code ((P).ambient (preparedRoot old e)) [] 0 0 := by
  have HR := prepared_seed_records old hv hd e he
  have HC : IntegralMixedCausalRecordPlanBits.count (preparedRoot old e)=
      (meaningfulCodes old e).length+tailCount old e := by
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [HR,WordListRecords.count_encode,List.length_append,List.length_replicate]
  have HF := meaningful_finish old e
  rw [prepared_initial] at HF
  have HB : b<N old+IntegralMixedCausalRecordPlanBits.count (preparedRoot old e) := by
    change b<FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+_ at hb1
    rw [prepared_initial] at hb1
    exact hb1
  have HI : b-N old-(meaningfulCodes old e).length<tailCount old e := by omega
  rw [IntegralMixedCausalRecordPlanBits.code,HR,WordList.get_encode,
    List.getElem?_append_right (by omega)]
  simp only [List.getElem?_replicate,HI,ite_true,Option.getD_some]

include hv hd he in
theorem seed_metadata_after_finish (b : ℕ) (hb0 : finishBirth old e≤b) (hb1 : b<fullBirth old e) :
    FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) b ∧
      FormulaSignSlotRadialProviderAtomic.selected (context (preparedRoot old e)) b=0 := by
  have HF := finish_eq old e
  rw [begin_eq] at HF
  have HB0 : N old≤b := by omega
  let i := b-N old
  have HB : b=FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+i := by
    rw [prepared_initial]
    dsimp only [i]
    omega
  have HI : i<IntegralMixedCausalRecordPlanBits.count (preparedRoot old e) := by
    change b<FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+_ at hb1
    rw [prepared_initial] at hb1
    dsimp only [i]
    omega
  have HG := IntegralMixedRoadmapChain.seed_point_good ((P).ambient (preparedRoot old e))
    (FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+i) 0 (Nat.zero_lt_succ _)
  have H := FormulaSignSlotRadialProviderRecordCriticalMetadata.frame_metadata (preparedRoot old e) i HI [] 0 0 HG
    (seed_code_after_finish old hv hd e he b hb0 hb1)
  exact ⟨Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) b) HB.symm) H.1,
    (congrArg (FormulaSignSlotRadialProviderAtomic.selected (context (preparedRoot old e))) HB).trans H.2⟩

include hv hd he in
theorem active_after_begin (b : ℕ) (hb0 : N old+start old≤b) (hb1 : b<fullBirth old e) :
    FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) b := by
  by_cases HT : finishBirth old e≤b
  · exact (seed_metadata_after_finish old hv hd e he b HT hb1).1
  have HF := finish_eq old e
  rw [begin_eq] at HF
  let a := N old+start old
  let k := dimension old-depth old
  by_cases HM : b=a
  · have H := (midpoint_anchor_metadata old hv hd e he).1
    exact Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) b) HM.symm) H
  by_cases HMC : b<a+1+k
  · let i := b-(a+1)
    have HI : i<dimension old-depth old := by dsimp only [i,a,k] at *;omega
    have H := (midpoint_capture_metadata old hv hd e he i HI).1
    have HE : N old+start old+1+i=b := by dsimp only [i,a] at *;omega
    exact Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) b) HE) H
  by_cases HC : b=a+1+k
  · have H := (child_anchor_metadata old hv hd e he).1
    exact Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) b) HC.symm) H
  · let i := b-(a+2+k)
    have HI : i<dimension old-depth old := by dsimp only [i,a,k] at *;omega
    have H := (child_capture_metadata old hv hd e he i HI).1
    have HE : N old+start old+2+(dimension old-depth old)+i=b := by dsimp only [i,a,k] at *;omega
    exact Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) b) HE) H

attribute [local irreducible] FormulaSignSlotRadialProviderFirstSeed.CutFreeAt
  IntegralFramedCreatingCut.IsCut IntegralMixedFramedRootPullback.instructionAt

include hv hd he in
theorem no_cut_after_begin (b : ℕ) (hb0 : N old+start old≤b) (hb1 : b<fullBirth old e) :
    FormulaSignSlotRadialProviderFirstSeed.CutFreeAt P D (preparedRoot old e) b := by
  have HA := active_after_begin old hv hd e he b hb0 hb1
  have HH : (FormulaSignSlotRadialProviderRecordPrefix.header (preparedRoot old e) b).context=1 := HA.2
  rw [FormulaSignSlotRadialProviderRecordPrefix.header_actual] at HH
  unfold FormulaSignSlotRadialProviderFirstSeed.CutFreeAt
  intro HC
  have HE := (IntegralFramedCreatingCut.isCut_iff_context _).mp HC
  rw [←IntegralMixedCommandHeaderBits.command_context,HH] at HE
  omega

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
