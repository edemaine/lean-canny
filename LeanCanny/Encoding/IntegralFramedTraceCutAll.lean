/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutExact
/-! # Exact native validity of every creating cut in one terminal trace

The quantifier ranges over literal chronological original instructions.
Each selected embedding is forced by the corresponding suffix of the
same terminal root, and every tested scalar is its actual retained bank
quotient. Integer/critical/default commands need no relative-cut guard.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutAll
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralFramedTraceCutScan (stagePacket StageCut)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)

private theorem parent_packet (q : List Bool) (j : ℕ) :
    IntegralFramedTraceCutGuards.parent P (stagePacket q j)=
      IntegralFramedTraceCutTask.task P (pair (pairFst q) (pair (List.replicate j true) [])) := by
  simp only [IntegralFramedTraceCutGuards.parent,Function.comp_apply,IntegralFramedTraceCutGuards.descriptor,
    IntegralFramedTraceCutGuards.root,stagePacket,pairFst_pair,pairSnd_pair]

include hFpos hf in
theorem stage_compatible_iff (q : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedTraceCutSource.input P D H L F C hs) (pairFst q) (pairSnd q))
    (j : ℕ) (hj : j<IntegralFramedTraceCutMetadata.length P D (pairFst q)+1)
    (hcut : StageCut P D (stagePacket q j)) :
    IntegralFramedTraceCutExact.Compatible P D H L F C hs (pairFst q) (List.replicate j true) (pairSnd q) hv ↔
      IntegralFramedTraceCutGuards.Guards P D H L F C hs hFpos hf (stagePacket q j) := by
  have HA:=IntegralFramedTraceCutOrigin.cut_active P D q j hj hcut
  rw [parent_packet] at HA
  have HC : IntegralFramedCreatingCut.ParentCut P D
      (IntegralFramedTraceCutTask.task P (pair (pairFst q) (pair (List.replicate j true) []))) := by
    change IntegralFramedCreatingCut.ParentCut P D (IntegralFramedTraceCutGuards.parent P (stagePacket q j)) at hcut
    simpa only [parent_packet] using hcut
  have HB:=IntegralFramedTraceCutOrigin.parent_birth P D q j hj
  rw [parent_packet] at HB
  have HS : birth P (IntegralFramedTraceCutTask.task P (pair (pairFst q) (pair (List.replicate j true) [])))=
      (List.replicate j true).length := by simpa only [List.length_replicate] using HB
  have HF : birth P (IntegralFramedTraceCutTask.task P (pair (pairFst q) (pair (List.replicate j true) [])))<
      (family P D H).birth (IntegralFramedTraceCutMetadata.terminal P D (pairFst q)) := by
    rw [HB,IntegralFramedTraceCutMetadata.terminal_birth]
    exact hj
  exact IntegralFramedTraceCutExact.compatible_iff P D H L F C hs hFpos hf
    (pairFst q) (List.replicate j true) (pairSnd q) hv HA HC HS HF

noncomputable def Validated (q : List Bool) : Prop :=
  ∃ hv : SquareSampleCompleteVertices.Valid (IntegralFramedTraceCutSource.input P D H L F C hs) (pairFst q) (pairSnd q),
    ∀ j<IntegralFramedTraceCutMetadata.length P D (pairFst q),
      IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D (pairFst q) j).command→
        IntegralFramedTraceCutExact.Compatible P D H L F C hs (pairFst q) (List.replicate j true) (pairSnd q) hv

include hFpos hf in
theorem validated_iff (q : List Bool) : Validated P D H L F C hs q ↔
    q∈IntegralFramedTraceCutScan.language P D H L F C hs hFpos hf := by
  constructor
  · rintro ⟨hv,hAll⟩
    refine ⟨hv,?_⟩
    intro j hj hc
    have HL:=IntegralFramedTraceCutOrigin.cut_lt_length P D q j hj hc
    have HI:=(IntegralFramedTraceCutOrigin.stageCut_iff P D q j hj).mp hc
    exact (stage_compatible_iff P D H L F C hs hFpos hf q hv j hj hc).mp (hAll j HL HI)
  · rintro ⟨hv,hAll⟩
    refine ⟨hv,?_⟩
    intro j hj hc
    have HJ : j<IntegralFramedTraceCutMetadata.length P D (pairFst q)+1:=hj.trans (Nat.lt_succ_self _)
    have HI:=(IntegralFramedTraceCutOrigin.stageCut_iff P D q j HJ).mpr hc
    exact (stage_compatible_iff P D H L F C hs hFpos hf q hv j HJ HI).mpr (hAll j HJ HI)

noncomputable def language : Language := {q | Validated P D H L F C hs q}

include hFpos hf in
theorem decider (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (hc : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hbc : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew hc) :
    SpaceDecider (language P D H L F C hs) := by
  apply (IntegralFramedTraceCutScan.decider P D H L F C hs hFpos hf a hL hF hC h0 h hb Hnew hc hbc).congr
  exact Set.ext (fun q=>(validated_iff P D H L F C hs hFpos hf q).symm)

end LeanCanny.Encoding.IntegralFramedTraceCutAll
