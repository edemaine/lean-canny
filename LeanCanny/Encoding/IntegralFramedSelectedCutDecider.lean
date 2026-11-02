/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutFiniteDecider
public import LeanCanny.Encoding.IntegralFramedCreatingCut
/-! # Original-header guard for native selected-cut tests

Only actual creating cut commands enter this language. An integer or
physical-critical command with a virtual fallback selection is rejected.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedSelectedCut
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
  q∈IntegralFramedCutFiniteGuards.language P D H L F C hs hFpos hf ∧
    IntegralFramedCreatingCut.ParentCut P D (pairFst q)}

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
  have EV:=(IntegralFramedCutFiniteGuards.decider P a D H L F C hs hL hF hC hFpos hf h hb h0 Hnew hc hbc).flagEvaluator
  have EC:=SpaceFunction.ofFP _ ((IntegralFramedCreatingCut.parentCut_FP P a D H h0).comp pairFst_mem_FP).flag_mem_FP
  have E:=EV.andFlags EC
  apply E.decider (fun v=>decide (v=[true])) (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.IntegralFramedSelectedCut
