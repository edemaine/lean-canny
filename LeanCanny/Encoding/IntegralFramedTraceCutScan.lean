/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutGuards
public import LeanCanny.Computation.SpaceFunctionQuantifiers
/-! # Native bounded scan of every actual creating cut at one terminal vertex

The unary loop runs through the original script plus one padded default.
Actual integer, physical-critical and default commands return true. Only
creating cut commands invoke the full finite guards, all on the same
terminal sampler context and vertex word.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutScan
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Brackets
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def StageCut (P : Parameters) (D : Plan P) (b : List Bool) :=
  IntegralFramedCreatingCut.ParentCut P D (IntegralFramedTraceCutGuards.parent P b)

theorem stageCut_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H) : FPPred (StageCut P D) :=
  (IntegralFramedCreatingCut.parentCut_FP P a D H h0).comp (IntegralFramedTraceCutGuards.parent_FP P a)

def stageQuery (b : List Bool) := pair (pair (pairFst (pairFst b)) (pairSnd (pairFst b))) (pairSnd b)
theorem stageQuery_FP : stageQuery∈FP:=mem_FP_pair
  (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP
def stagePacket (q : List Bool) (j : ℕ) := pair (pair (pairFst q) (pairSnd q)) (List.replicate j true)

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)

noncomputable def language : Language := {q |
  SquareSampleCompleteVertices.Valid (IntegralFramedTraceCutSource.input P D H L F C hs) (pairFst q) (pairSnd q) ∧
    ∀ j<IntegralFramedTraceCutMetadata.length P D (pairFst q)+1,
      StageCut P D (stagePacket q j)→
        IntegralFramedTraceCutGuards.Guards P D H L F C hs hFpos hf (stagePacket q j)}

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
    SpaceDecider (language P D H L F C hs hFpos hf) := by
  have EA:=IntegralFramedCurrentQSquare.access_native P a D H Hnew hc hbc L F C hs hL hF hC
    (IntegralFramedTraceCutMetadata.terminal P D) (IntegralFramedTraceCutMetadata.terminal_FP P D H h0)
    (IntegralFramedTraceCutMetadata.terminal_positive P D H)
  have EV:=(SquareSampleCompleteVertices.decider EA).flagEvaluator
  have EG:=IntegralFramedTraceCutGuards.evaluator P D H L F C hs hFpos hf a hL hF hC h0 h hb Hnew hc hbc
  have E:=SpaceFunction.branch (fun b=>decide (StageCut P D b)) (stageCut_FP P a D H h0).flag_mem_FP EG
    (SpaceFunction.ofFP _ (constFn_mem_FP [true]))
  have EI : SpaceFunction (fun b=>[decide (StageCut P D b→IntegralFramedTraceCutGuards.Guards P D H L F C hs hFpos hf b)]) := E.congr (by
    funext b
    by_cases HB:StageCut P D b <;> simp only [HB,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false,true_implies,false_implies,decide_true])
  have HM : UnaryFn (fun q=>IntegralFramedTraceCutMetadata.length P D (pairFst q)+1):=
    ((IntegralFramedTraceCutMetadata.length_unary P D H h0).comp pairFst_mem_FP).add (UnaryFn.const 1)
  have EI0:=EI.precompose stageQuery stageQuery_FP
  have EU:=(EI0.forall_unary HM).congr (show _=(fun q=>[decide (∀ j<IntegralFramedTraceCutMetadata.length P D (pairFst q)+1,
      StageCut P D (stagePacket q j)→IntegralFramedTraceCutGuards.Guards P D H L F C hs hFpos hf (stagePacket q j))]) by
    funext q
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,stageQuery,stagePacket,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])
  apply (EV.andFlags EU).decider (fun v=>decide (v=[true])) (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]
  rfl

end LeanCanny.Encoding.IntegralFramedTraceCutScan
