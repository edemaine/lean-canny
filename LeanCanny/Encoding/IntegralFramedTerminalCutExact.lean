/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutGuardComplete
public import LeanCanny.Encoding.IntegralFramedTerminalCutDecider
/-! # Exact native validation of earlier selected cuts at one terminal root

The interpretation, specialized degree and full factor root all refer to
the literal suffix of one complete terminal tuple. The scalar denominator
is the actual earlier normalized cut denominator, with no raw-leading or
absolute-norm substitution.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutExact
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Brackets
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)
  (key : List Bool→List Bool) (hpos : ∀ q,0<(family P D H).birth (key q))
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w)
  (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
local notation "G" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "old" => IntegralMixedCutSource.Family.state G parent
local notation "degree" => IntegralMixedCutSource.Family.degree G parent
local notation "rule" => IntegralMixedCutSource.Family.rule G parent
local notation "kind" => IntegralMixedCutSource.Family.kind G parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G parent
local notation "factor" => IntegralMixedRelativeCuts.factor old bound rule kind
local notation "z" => IntegralFramedCompleteSuffix.joint P D H L F C hs key hpos c w hv
local notation "cutTuple" => (fun i : Fin (IntegralMixedCutSource.Family.birth G parent+1)=>
  z (Fin.val i+(IntegralMixedCutSource.Family.birth G (key c)-(birth P c+1))))
local notation "sample" => Subtype.val (SquareSampleCompleteVertices.candidate (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w hv)
omit hFpos hf ha in
noncomputable def Compatible : Prop :=
  ∃ φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+((G).birth (key c)-(G).birth parent))^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (2^(G).width parent) ((G).birth parent) i) ∧
    IntegralMixedRelativeCuts.Valid old bound rule φ kind ∧ ((factor).map φ.toRingHom).natDegree=degree ∧
    (factor).eval₂ φ.toRingHom (IntegralRelativeTruncation.jointQuotient (old).sampler.scalarPrefix factor degree cutTuple)=0

include ha in
theorem compatible_iff (hcut : IntegralFramedCreatingCut.ParentCut P D c)
    (hroot : pairFst (key c)=RankedHistoryTask.root c) (hfit : birth P c<(G).birth (key c)) :
    Compatible P D H L F C hs key hpos c w hv ↔
      IntegralFramedTerminalCutGuards.Guards P D H L F C hs hFpos hf key hpos (pair c w) := by
  constructor
  · rintro ⟨φ,hφ,hvalid,hd,hr⟩
    exact IntegralFramedTerminalCutGuardComplete.guards P D H L F C hs hFpos hf key hpos c w hv ha hfit φ hφ hvalid hd hr
  · exact IntegralFramedTerminalCutAcceptedRoot.exists_root P D H L F C hs hFpos hf key hpos c w hv ha hcut hroot hfit

omit hFpos hf hv ha in
noncomputable def Accepted : Prop :=
  ∃ hv : SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w,
    IntegralMixedFramedFullCutProbeBits.Active P c ∧ IntegralFramedCreatingCut.ParentCut P D c ∧
    pairFst (key c)=RankedHistoryTask.root c ∧ birth P c<(G).birth (key c) ∧ Compatible P D H L F C hs key hpos c w hv

omit hv ha in
theorem accepted_iff : Accepted P D H L F C hs key hpos c w ↔
    pair c w∈IntegralFramedTerminalCutGuards.language P D H L F C hs hFpos hf key hpos := by
  constructor
  · rintro ⟨hv,ha,hcut,hroot,hfit,hcomp⟩
    exact ⟨by simpa only [pairFst_pair,pairSnd_pair] using hv,
      by simpa only [pairFst_pair] using ha,by simpa only [pairFst_pair] using hcut,
      by simpa only [pairFst_pair] using hroot,by simpa only [pairFst_pair,IntegralFramedTerminalCutTest.count] using hfit,
      (compatible_iff P D H L F C hs hFpos hf key hpos c w hv ha hcut hroot hfit).mp hcomp⟩
  · rintro ⟨hv,ha,hcut,hroot,hfit,hg⟩
    simp only [pairFst_pair,pairSnd_pair] at hv ha hcut hroot hfit
    exact ⟨hv,ha,hcut,hroot,hfit,(compatible_iff P D H L F C hs hFpos hf key hpos c w hv ha hcut hroot hfit).mpr hg⟩

omit hFpos hf c w hv ha in
noncomputable def language : Language := {q | Accepted P D H L F C hs key hpos (pairFst q) (pairSnd q)}

omit c w hv ha in
include hFpos hf in
theorem decider (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hk : key∈FP)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (hc : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hbc : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew hc) : SpaceDecider (language P D H L F C hs key hpos) := by
  have E:=(IntegralFramedTerminalCutGuards.decider P D H L F C hs hFpos hf key hpos a hL hF hC hk h hb h0 Hnew hc hbc).flagEvaluator
  have EQ:=E.precompose (fun q=>pair (pairFst q) (pairSnd q)) (mem_FP_pair pairFst_mem_FP pairSnd_mem_FP)
  apply EQ.decider (fun v=>decide (v=[true])) (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [Function.comp_apply,language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]
  exact accepted_iff P D H L F C hs hFpos hf key hpos (pairFst q) (pairSnd q)

end LeanCanny.Encoding.IntegralFramedTerminalCutExact
