/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutExact
public import LeanCanny.Encoding.IntegralFramedTerminalCutBankPoint
/-! # Exact native selected-cut validation at actual terminal bank points

The point uses the same complete terminal tuple, original fixed powers,
and actual retained integer denominator. No raw leading, independent
coordinate roots or coefficient oracle replaces this point.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutBankExact
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
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
local notation "bankPoint" => IntegralMixedFramedBankObservation.Data.point
  (IntegralMixedFramedBankObservation.ofState (IntegralMixedCutSource.Family.state G (key c))) z
    (IntegralMixedCutSource.Family.birth G (key c)-birth P c-1)

omit hFpos hf ha in
noncomputable def Compatible : Prop :=
  ∃ φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+((G).birth (key c)-(G).birth parent))^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (2^(G).width parent) ((G).birth parent) i) ∧
    IntegralMixedRelativeCuts.Valid old bound rule φ kind ∧ ((factor).map φ.toRingHom).natDegree=degree ∧
    (factor).eval₂ φ.toRingHom bankPoint=0

omit hFpos hf in
include ha in
theorem compatible_iff (hcut : IntegralFramedCreatingCut.ParentCut P D c)
    (hroot : pairFst (key c)=RankedHistoryTask.root c) (hfit : birth P c<(G).birth (key c)) :
    Compatible P D H L F C hs key hpos c w hv ↔IntegralFramedTerminalCutExact.Compatible P D H L F C hs key hpos c w hv := by
  have HP:=IntegralFramedTerminalCutBankPoint.point_eq P D H c (key c) ha hcut hroot hfit z
  simp only [Compatible,IntegralFramedTerminalCutExact.Compatible,HP]

include ha in
theorem guards_iff (hcut : IntegralFramedCreatingCut.ParentCut P D c)
    (hroot : pairFst (key c)=RankedHistoryTask.root c) (hfit : birth P c<(G).birth (key c)) :
    Compatible P D H L F C hs key hpos c w hv ↔
      IntegralFramedTerminalCutGuards.Guards P D H L F C hs hFpos hf key hpos (pair c w) :=
  (compatible_iff P D H L F C hs key hpos c w hv ha hcut hroot hfit).trans
    (IntegralFramedTerminalCutExact.compatible_iff P D H L F C hs hFpos hf key hpos c w hv ha hcut hroot hfit)

omit hFpos hf hv ha in
noncomputable def Accepted : Prop :=
  ∃ hv : SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w,
    IntegralMixedFramedFullCutProbeBits.Active P c ∧ IntegralFramedCreatingCut.ParentCut P D c ∧
    pairFst (key c)=RankedHistoryTask.root c ∧ birth P c<(G).birth (key c) ∧ Compatible P D H L F C hs key hpos c w hv

omit hFpos hf hv ha in
theorem accepted_iff : Accepted P D H L F C hs key hpos c w ↔IntegralFramedTerminalCutExact.Accepted P D H L F C hs key hpos c w := by
  constructor
  · rintro ⟨hv,ha,hcut,hroot,hfit,hcomp⟩
    exact ⟨hv,ha,hcut,hroot,hfit,(compatible_iff P D H L F C hs key hpos c w hv ha hcut hroot hfit).mp hcomp⟩
  · rintro ⟨hv,ha,hcut,hroot,hfit,hcomp⟩
    exact ⟨hv,ha,hcut,hroot,hfit,(compatible_iff P D H L F C hs key hpos c w hv ha hcut hroot hfit).mpr hcomp⟩

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
  have E:=IntegralFramedTerminalCutExact.decider P D H L F C hs hFpos hf key hpos a hL hF hC hk h hb h0 Hnew hc hbc
  apply E.congr
  apply Set.ext
  intro q
  exact (accepted_iff P D H L F C hs key hpos (pairFst q) (pairSnd q)).symm

end LeanCanny.Encoding.IntegralFramedTerminalCutBankExact
