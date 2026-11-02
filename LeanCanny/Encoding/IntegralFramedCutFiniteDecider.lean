/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutFiniteGuards
/-! # Native complete-vertex selected-cut guard language

This language includes original complete-vertex validity and the active
parent guard. All finite coefficient and newest-root tests reuse that
one vertex. No relative-validity or factor-root decision is a premise.
The semantic identification with an actual creating cut is separate.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutFiniteGuards
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Brackets
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCutProbeTaskBits (parameters)
open IntegralMixedFramedCutProbeTransportBits (plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (a : Access P) (D : Plan P)
  (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
  (hFpos : ∀ root,1≤F root)
  (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
  (h : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D H L F C))
  (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D H L F C) h)



noncomputable def language : Language := {q |
  SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) (pairFst q) (pairSnd q) ∧
    IntegralMixedFramedFullCutProbeBits.Active P (pairFst q) ∧ Guards P D H L F C hs hFpos hf q}

include a hL hF hC h hb in
theorem decider
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (hc : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hbc : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew hc) :
    SpaceDecider (language P D H L F C hs hFpos hf) := by
  have EA:=IntegralFramedCutSuccessor.access P a D H Hnew hc hbc L F C hs hL hF hC
  have EV:=(SquareSampleCompleteVertices.decider EA).flagEvaluator
  have EAct:=SpaceFunction.ofFP _ ((IntegralMixedFramedFullCutProbeBits.active_FP P a).comp pairFst_mem_FP).flag_mem_FP
  have EG:=evaluator P a D H L F C hs hL hF hC hFpos hf h hb h0 Hnew hc hbc
  have E:=EV.andFlags (EAct.andFlags EG)
  apply E.decider (fun v=>decide (v=[true])) (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,SquareSampleCompleteVertices.language,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.IntegralFramedCutFiniteGuards
