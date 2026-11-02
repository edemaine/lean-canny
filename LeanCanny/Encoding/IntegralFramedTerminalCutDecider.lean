/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutGuards
public import LeanCanny.Encoding.IntegralFramedCreatingCut
/-! # Original-only native selected-cut guard language at one terminal vertex

The terminal vertex, original creating-cut header, parent activity and
chronological room are checked before the finite sign guards. Exact
factor-root semantics are supplied separately through the same tuple.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutGuards
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Brackets
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)
  (key : List Bool→List Bool) (hpos : ∀ q,0<(family P D H).birth (key q))

noncomputable def language : Language := {q |
  SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) (pairFst q) (pairSnd q) ∧
    IntegralMixedFramedFullCutProbeBits.Active P (pairFst q) ∧
    IntegralFramedCreatingCut.ParentCut P D (pairFst q) ∧
    pairFst (key (pairFst q))=RankedHistoryTask.root (pairFst q) ∧
    birth P (pairFst q)<IntegralFramedTerminalCutTest.count P D H key (pairFst q) ∧
    Guards P D H L F C hs hFpos hf key hpos q}

theorem decider (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hk : key∈FP)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (hc : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hbc : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew hc) :
    SpaceDecider (language P D H L F C hs hFpos hf key hpos) := by
  have EA:=IntegralFramedCurrentQSquare.access_native P a D H Hnew hc hbc L F C hs hL hF hC key hk hpos
  have EV:=(SquareSampleCompleteVertices.decider EA).flagEvaluator
  have EAct:=SpaceFunction.ofFP _ ((IntegralMixedFramedFullCutProbeBits.active_FP P a).comp pairFst_mem_FP).flag_mem_FP
  have ECmd:=SpaceFunction.ofFP _ ((IntegralFramedCreatingCut.parentCut_FP P a D H h0).comp pairFst_mem_FP).flag_mem_FP
  have HB : BinaryFn (fun q=>birth P (pairFst q)):=BinaryFn.ofUnary ((IntegralMixedOldHeightBits.birth_unary P a).comp pairFst_mem_FP)
  have HC : BinaryFn (fun q=>IntegralFramedTerminalCutTest.count P D H key (pairFst q)):=
    BinaryFn.ofUnary ((IntegralFramedTerminalCutTest.count_unary P a D H key hk).comp pairFst_mem_FP)
  have ERoot:=SpaceFunction.ofFP _ (stringEq_fppred
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP hk) pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP RankedHistoryTask.root_FP)).flag_mem_FP
  have EFit:=SpaceFunction.ofFP _ (HB.lt HC).flag_mem_FP
  have EG:=evaluator P D H L F C hs hFpos hf key hpos a hL hF hC hk h hb h0 Hnew hc hbc
  have E:=EV.andFlags (EAct.andFlags (ECmd.andFlags (ERoot.andFlags (EFit.andFlags EG))))
  apply E.decider (fun v=>decide (v=[true])) (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [Function.comp_apply,language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.IntegralFramedTerminalCutGuards
