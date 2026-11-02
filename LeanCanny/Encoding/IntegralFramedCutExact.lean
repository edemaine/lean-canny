/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutGuardComplete
public import LeanCanny.Encoding.IntegralFramedSelectedCutDecider
/-! # Exact polynomial-space validation of actual selected cuts

The semantic predicate uses the one decoded complete successor root, its
literal parent tail, and its actual newest retained quotient. It checks
all four full factor kinds before truncation. No relative-validity,
coefficient, denominator or factor-root oracle is an input.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutExact
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Brackets
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w)
  (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
local notation "model" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "oldState" => IntegralMixedCutSource.Family.state model parent
local notation "rule" => IntegralMixedCutSource.Family.rule model parent
local notation "kind" => IntegralMixedCutSource.Family.kind model parent
local notation "degree" => IntegralMixedCutSource.Family.degree model parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound model parent
local notation "factor" => IntegralMixedRelativeCuts.factor oldState bound rule kind
local notation "chosen" => IntegralMixedRawKindBits.choice model parent
local notation "sample" => Subtype.val (SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv)
local notation "oldTuple" => (fun i : Fin (IntegralMixedCutSource.Family.birth model parent+1)=>
  sample (Fin.cast (IntegralFramedCutCommonParent.dimension P D H L F C hs c ha) i))
local notation "bankPoint" => IntegralMixedFramedBankObservation.Data.point
  (IntegralMixedFramedBankObservation.ofState (IntegralMixedCutSource.Family.state model (IntegralFramedCutSuccessor.key P c)))
  (IntegralFramedCutParentInterpretation.joint P D H L F C hs c w hv) 0
local notation "sign" => IntegralFramedCutCoefficientTest.value P D H L F C hs hFpos hf

omit hFpos hf in
noncomputable def Compatible : Prop :=
  ∃ φ : (oldState).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀ i,φ ((oldState).sampler.scalarPrefix.basis.generator i)=oldTuple i.succ^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (2^(model).width parent) ((model).birth parent) i) ∧
    IntegralMixedRelativeCuts.Valid oldState bound rule φ kind ∧
    ((factor).map φ.toRingHom).natDegree=degree ∧ (factor).eval₂ φ.toRingHom bankPoint=0

 theorem compatible_iff (hcut : IntegralFramedCreatingCut.ParentCut P D c) :
    Compatible P D H L F C hs c w hv ha ↔
      IntegralFramedCutFiniteGuards.Guards P D H L F C hs hFpos hf (pair c w) := by
  constructor
  · rintro ⟨φ,hφ,hvalid,hd,hr⟩
    exact IntegralFramedCutGuardComplete.guards P D H L F C hs hFpos hf c w hv ha hcut φ hφ hvalid hd hr
  · exact IntegralFramedCutBankRoot.exists_root P D H L F C hs hFpos hf c w hv ha hcut

omit hFpos hf hv ha in
noncomputable def Accepted : Prop :=
  ∃ hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w,
  ∃ ha : IntegralMixedFramedFullCutProbeBits.Active P c,
    IntegralFramedCreatingCut.ParentCut P D c ∧ Compatible P D H L F C hs c w hv ha

omit hv ha in
theorem accepted_iff : Accepted P D H L F C hs c w ↔
    pair c w∈IntegralFramedSelectedCut.language P D H L F C hs hFpos hf := by
  constructor
  · rintro ⟨hv,ha,hcut,hcomp⟩
    exact ⟨⟨by simpa only [pairFst_pair,pairSnd_pair] using hv,
      by simpa only [pairFst_pair] using ha,(compatible_iff P D H L F C hs hFpos hf c w hv ha hcut).mp hcomp⟩,
      by simpa only [pairFst_pair] using hcut⟩
  · rintro ⟨⟨hv,ha,hg⟩,hcut⟩
    simp only [pairFst_pair,pairSnd_pair] at hv ha hcut
    exact ⟨hv,ha,hcut,(compatible_iff P D H L F C hs hFpos hf c w hv ha hcut).mpr hg⟩

omit hFpos hf c w hv ha in
noncomputable def language : Language := {q | Accepted P D H L F C hs (pairFst q) (pairSnd q)}

omit c w hv ha in
include hFpos hf in
theorem decider (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls
      (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C)
      (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds
      (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C)
      (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (hc : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hbc : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew hc) :
    SpaceDecider (language P D H L F C hs) := by
  have E:=(IntegralFramedSelectedCut.decider P a D H L F C hs hL hF hC hFpos hf h hb h0 Hnew hc hbc).flagEvaluator
  have EQ:=E.precompose (fun q=>pair (pairFst q) (pairSnd q)) (mem_FP_pair pairFst_mem_FP pairSnd_mem_FP)
  apply EQ.decider (fun v=>decide (v=[true])) (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [Function.comp_apply,language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]
  exact accepted_iff P D H L F C hs hFpos hf (pairFst q) (pairSnd q)

end LeanCanny.Encoding.IntegralFramedCutExact
