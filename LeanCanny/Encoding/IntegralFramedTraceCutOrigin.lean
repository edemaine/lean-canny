/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutScan
/-! # Chronological cut guards read literal creating commands

The bounded scan ranges over the original script plus its integer default.
Every tested cut is in range and automatically has a valid virtual query;
no creating-command or active-query premise is supplied by the caller.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutOrigin
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralFramedTraceCutGuards (parent)
open IntegralFramedTraceCutScan (stagePacket StageCut)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem stage_bound (P : Parameters) (D : Plan P) (q : List Bool) (j : ℕ)
    (hj : j<IntegralFramedTraceCutMetadata.length P D (pairFst q)+1) : j≤birthCap P (pairFst q) := by
  have HR:=D.room (pairFst q)
  change j≤P.cap (pairFst q)+1
  unfold IntegralFramedTraceCutMetadata.length at hj
  omega

theorem parent_root (P : Parameters) (q : List Bool) (j : ℕ) :
    RankedHistoryTask.root (parent P (stagePacket q j))=pairFst q := by
  simp only [parent,Function.comp_apply,IntegralFramedTraceCutGuards.descriptor,IntegralFramedTraceCutGuards.root,
    stagePacket,pairFst_pair,pairSnd_pair,IntegralFramedTraceCutTask.task_root]

theorem parent_birth (P : Parameters) (D : Plan P) (q : List Bool) (j : ℕ)
    (hj : j<IntegralFramedTraceCutMetadata.length P D (pairFst q)+1) :
    birth P (parent P (stagePacket q j))=j := by
  have HB:=stage_bound P D q j hj
  unfold parent
  rw [Function.comp_apply,IntegralFramedTraceCutTask.task_birth]
  · simp only [IntegralFramedTraceCutGuards.descriptor,IntegralFramedTraceCutGuards.root,stagePacket,
      pairFst_pair,pairSnd_pair,IntegralFramedTraceCutTask.stage_packet,List.length_replicate]
  · simpa only [IntegralFramedTraceCutGuards.descriptor,IntegralFramedTraceCutGuards.root,stagePacket,
      pairFst_pair,pairSnd_pair,IntegralFramedTraceCutTask.stage_packet,List.length_replicate] using HB

attribute [local irreducible] IntegralFramedTraceCutTask.task

theorem parent_saved (P : Parameters) (D : Plan P) (q : List Bool) (j : ℕ)
    (hj : j<IntegralFramedTraceCutMetadata.length P D (pairFst q)+1) :
    IntegralMixedVirtualTaskBits.saved P (parent P (stagePacket q j))=
      IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst q) j (BinaryNatCode.encode 2) := by
  unfold IntegralMixedVirtualTaskBits.saved
  rw [parent_root,parent_birth P D q j hj]
  have HH : get P .slot15 (parent P (stagePacket q j))=2 := by
    exact IntegralFramedTraceCutTask.task_context P (IntegralFramedTraceCutGuards.descriptor (stagePacket q j))
  rw [HH]

theorem stageCut_iff (P : Parameters) (D : Plan P) (q : List Bool) (j : ℕ)
    (hj : j<IntegralFramedTraceCutMetadata.length P D (pairFst q)+1) :
    StageCut P D (stagePacket q j) ↔
      IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D (pairFst q) j).command := by
  unfold StageCut IntegralFramedCreatingCut.ParentCut
  rw [parent_saved P D q j hj]
  have HP:=IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P (pairFst q) j (BinaryNatCode.encode 2)
    (stage_bound P D q j hj)
  have HR:=IntegralMixedFramedHistoryFamilyBits.keyAt_root (pairFst q) j (BinaryNatCode.encode 2)
  have HE : HEq (IntegralMixedFramedHistoryFamilyBits.instruction P D
      (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst q) j (BinaryNatCode.encode 2)))
      (IntegralMixedFramedRootPullback.instructionAt P D (pairFst q) j) :=
    IntegralMixedFramedRootPullback.instructionAt_congr P D _ (pairFst q) _ j HR HP
  exact Iff.of_eq (IntegralMixedFramedRootPullback.instruction_read
    (fun _ _ I=>IntegralFramedCreatingCut.IsCut I.command) _ _
    (congrArg P.ambient HR) (congrArg P.width HR) HE)


theorem cut_lt_length (P : Parameters) (D : Plan P) (q : List Bool) (j : ℕ)
    (hj : j<IntegralFramedTraceCutMetadata.length P D (pairFst q)+1)
    (hc : StageCut P D (stagePacket q j)) : j<IntegralFramedTraceCutMetadata.length P D (pairFst q) :=
  IntegralFramedTraceCutMetadata.cut_lt_length P D _ _ ((stageCut_iff P D q j hj).mp hc)

theorem cut_active (P : Parameters) (D : Plan P) (q : List Bool) (j : ℕ)
    (hj : j<IntegralFramedTraceCutMetadata.length P D (pairFst q)+1)
    (hc : StageCut P D (stagePacket q j)) :
    IntegralMixedFramedFullCutProbeBits.Active P (parent P (stagePacket q j)) := by
  refine ⟨?_,?_⟩
  · unfold IntegralMixedVirtualCaps.valid
    rw [parent_birth P D q j hj,parent_root]
    exact IntegralFramedTraceCutMetadata.cut_lt_cap P D _ _ ((stageCut_iff P D q j hj).mp hc)
  · change 2≤get P .slot15 (parent P (stagePacket q j)) ∧ get P .slot15 (parent P (stagePacket q j))≤4
    have HH : get P .slot15 (parent P (stagePacket q j))=2 :=
      IntegralFramedTraceCutTask.task_context P (IntegralFramedTraceCutGuards.descriptor (stagePacket q j))
    rw [HH]
    decide

theorem default_not_cut (P : Parameters) (D : Plan P) (q : List Bool) :
    ¬StageCut P D (stagePacket q (IntegralFramedTraceCutMetadata.length P D (pairFst q))) := by
  intro hc
  have HL:=cut_lt_length P D q _ (Nat.lt_succ_self _) hc
  exact (Nat.lt_irrefl _) HL

end LeanCanny.Encoding.IntegralFramedTraceCutOrigin
