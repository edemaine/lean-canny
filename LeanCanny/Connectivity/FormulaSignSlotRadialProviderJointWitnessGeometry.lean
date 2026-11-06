/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderStratumLabelGeometry
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderJointWitnessNative
/-! # One bounded native witness is exactly one doubly labelled stratum sample

The two anchored seed pairs refer to the same stratum kind, Gamma table and
own sampler word. Component sampling preserves both labels simultaneously.
This theorem does not assert the separate grid or cut guards of a descriptor.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderJointWitnessGeometry
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open CoerciveComponentSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "JW" => FormulaSignSlotRadialProviderJointWitness.language
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider" => FormulaSignSlotRadialProviderAtomic.provider

private theorem sampled_zero (S : IntegralFramedBankPolynomialModel.Source)
    (hp : ∀u,0<S.arity u) (u c w:List Bool) (hc:ImplicitSourceGramGrid.header c=u)
    (hq:pair c w∈ImplicitSourceComponentSampler.language S hp):
    ∃hw:SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input S hp) c w,
      ∃x:Zeros ((S.polynomial u).map (Int.castRingHom ℝ)),
        HEq (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c w hw).val x.val:=by
  cases hc
  have hw:SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input S hp) c w:=by
    simpa only [pairFst_pair,pairSnd_pair] using hq.1
  refine ⟨hw,⟨(SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c w hw).val,?_⟩,HEq.rfl⟩
  change MvPolynomial.eval _ ((S.polynomial (ImplicitSourceGramGrid.header c)).map (Int.castRingHom ℝ))=0
  simpa only [MvPolynomial.eval_map] using (ImplicitSourceComponentSampler.packet S hp c w hw).mp hq

private theorem label_packet (H:List Bool) (k:ℕ) (side:Bool):
    FormulaSignSlotRadialJointStratumLabels.label side (FormulaSignSlotRadialJointStratum.packet H k)=
      FormulaSignSlotRadialProviderJointWitness.label side H:=by
  simp only [FormulaSignSlotRadialJointStratumLabels.label,FormulaSignSlotRadialJointStratum.header,
    FormulaSignSlotRadialJointStratum.packet,pairFst_pair,FormulaSignSlotRadialProviderJointWitness.label]

private theorem good_packet (H:List Bool) (k:ℕ) (side:Bool):
    FormulaSignSlotRadialJointStratumLabels.Good side (FormulaSignSlotRadialJointStratum.packet H k) ↔
      AuxiliaryCandidateComponentCover.Good CanonicalAuxiliaryCandidateCover.dimension_unary
        CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope
        (FormulaSignSlotRadialJointLayout.source side H) (FormulaSignSlotRadialProviderJointWitness.label side H):=by
  unfold FormulaSignSlotRadialJointStratumLabels.Good
  rw [FormulaSignSlotRadialProviderExternalLabelGeometry.source_packet,label_packet]

attribute [local irreducible] SquareSampleCompleteVertices.Valid SquareSampleCompleteVertices.candidate
  ImplicitSourceGramGrid.input CanonicalAuxiliaryCandidateCover.dimension CanonicalAuxiliaryCandidateCover.equation
  FormulaSignSlotRadialProviderAtomic.Valid FormulaSignSlotRadialProviderAtomic.field
  FormulaSignSlotRadialProviderAtomic.depth
  FormulaSignSlotRadialProviderAnchoredAssociation.language

private theorem seed_pair_atLabel (H:List Bool) (k:ℕ) (Gamma w:List Bool)
    (hw:SquareSampleCompleteVertices.Valid F (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w)
    (hq:pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language)
    (x:FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H k))
    (hx:HEq (SquareSampleCompleteVertices.candidate F (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w hw).val x.val)
    (side:Bool) (a e:List Bool) (hs:FormulaSignSlotRadialProviderJointWitness.SeedPair H k Gamma w side a e):
    FormulaSignSlotRadialJointStratumLabels.AtLabel side (FormulaSignSlotRadialJointStratum.packet H k) x:=by
  have HA:=(FormulaSignSlotRadialProviderAnchoredAssociation.language_iff a e).mp hs.2.2
  have HVa:A a:=by
    simpa only [FormulaSignSlotRadialProviderAssociation.Guards,FormulaSignSlotRadialProviderAssociation.left,pairFst_pair] using HA.1.1.1
  have HVe:A e:=by
    simpa only [FormulaSignSlotRadialProviderAssociation.Guards,FormulaSignSlotRadialProviderAssociation.right,pairSnd_pair] using HA.1.1.2.1
  have HH:FormulaSignSlotRadialProviderAssociation.Header (pair a e):=HA.1.1.2.2
  have HD:FormulaSignSlotRadialProviderAtomic.depth a=0 ∧FormulaSignSlotRadialProviderAtomic.depth e=0:=by
    simp only [FormulaSignSlotRadialProviderAssociation.Header,
      FormulaSignSlotRadialProviderAssociation.left,FormulaSignSlotRadialProviderAssociation.right,
      pairFst_pair,pairSnd_pair] at HH
    exact ⟨HH.1,HH.2.1⟩
  apply (FormulaSignSlotRadialProviderStratumLabelGeometry.atLabel_iff_exists_anchored_pair H k Gamma side w hw hq x hx).mpr
  refine ⟨a,e,HVa,HVe,?_,?_,HD.1,HD.2,hs.2.2⟩
  · simpa only [label_packet] using hs.1
  · simpa only [label_packet] using hs.2.1

/-- One actual own sampler tuple supplies both anchored native seed pairs.
All original-header witness bounds are obtained by the native encoder. -/
theorem of_sampled_point (H:List Bool) (k:ℕ) (Gamma w:List Bool)
    (hGamma:Gamma.length≤FormulaSignSlotRadialJointStratumSampler.tableBound (FormulaSignSlotRadialJointStratum.packet H k))
    (hw:SquareSampleCompleteVertices.Valid F (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w)
    (hq:pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language)
    (x:FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H k))
    (hx:HEq (SquareSampleCompleteVertices.candidate F (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w hw).val x.val)
    (HB:FormulaSignSlotRadialJointStratumLabels.BothLabels (FormulaSignSlotRadialJointStratum.packet H k) x):H∈JW:=by
  obtain ⟨aL,eL,_haL,_heL,HLa,HLe,_hdL,_hdeL,HL⟩:=
    (FormulaSignSlotRadialProviderStratumLabelGeometry.atLabel_iff_exists_anchored_pair H k Gamma false w hw hq x hx).mp (HB false)
  obtain ⟨aR,eR,_haR,_heR,HRa,HRe,_hdR,_hdeR,HR⟩:=
    (FormulaSignSlotRadialProviderStratumLabelGeometry.atLabel_iff_exists_anchored_pair H k Gamma true w hw hq x hx).mp (HB true)
  apply FormulaSignSlotRadialProviderJointWitness.of_seed_pairs H k Gamma w aL eL aR eR hGamma hq
  · intro side
    have HG:=(HB side).choose
    exact (good_packet H k side).mp HG
  · exact ⟨by simpa only [label_packet] using HLa,by simpa only [label_packet] using HLe,HL⟩
  · exact ⟨by simpa only [label_packet] using HRa,by simpa only [label_packet] using HRe,HR⟩

/-- A bounded certificate retains its actual decoded sampler point and both
prescribed labels. The polynomial and table are not sampled again. -/
theorem language_iff_sampled (H:List Bool):H∈JW ↔
    ∃k:ℕ,∃Gamma w:List Bool,
      k≤FormulaSignSlotRadialProviderOriginalBudget.featureCount H ∧
      Gamma.length≤FormulaSignSlotRadialProviderOriginalBudget.tableBudget H ∧
      w.length≤FormulaSignSlotRadialProviderOriginalBudget.ownwordBudget H ∧
      Gamma.length≤FormulaSignSlotRadialJointStratumSampler.tableBound (FormulaSignSlotRadialJointStratum.packet H k) ∧
      pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language ∧
      ∃hw:SquareSampleCompleteVertices.Valid F (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w,
        ∃x:FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H k),
          FormulaSignSlotRadialJointStratumLabels.BothLabels (FormulaSignSlotRadialJointStratum.packet H k) x ∧
          HEq (SquareSampleCompleteVertices.candidate F (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w hw).val x.val:=by
  constructor
  · intro HL
    obtain ⟨k,Gamma,w,aL,eL,aR,eR,HS,HG,HQ,HL,HR⟩:=
      (FormulaSignSlotRadialProviderJointWitness.language_iff H).mp HL
    obtain ⟨hw,x,hx⟩:=sampled_zero FormulaSignSlotRadialJointStratum.source FormulaSignSlotRadialJointStratumSampler.positive
      (FormulaSignSlotRadialJointStratum.packet H k) (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w
      (pairFst_pair _ _) HQ
    refine ⟨k,Gamma,w,HS.1,HS.2.1,HS.2.2.1,HG,HQ,hw,x,?_,hx⟩
    intro side
    cases side
    · exact seed_pair_atLabel H k Gamma w hw HQ x hx false aL eL HL
    · exact seed_pair_atLabel H k Gamma w hw HQ x hx true aR eR HR
  · rintro ⟨k,Gamma,w,_HK,_HG,_HW,HT,HQ,hw,x,HB,hx⟩
    exact of_sampled_point H k Gamma w HT hw HQ x hx HB

/-- Native shared-witness membership is exactly nonempty intersection of the
two literal component labels on some actual compact stratum. -/
theorem language_iff_labels (H:List Bool):H∈JW ↔
    ∃k:ℕ,∃x:FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H k),
      FormulaSignSlotRadialJointStratumLabels.BothLabels (FormulaSignSlotRadialJointStratum.packet H k) x:=by
  constructor
  · intro HL
    obtain ⟨k,_Gamma,_w,_HK,_HG,_HW,_HT,_HQ,_hw,x,HB,_hx⟩:=(language_iff_sampled H).mp HL
    exact ⟨k,x,HB⟩
  · rintro ⟨k,x,HB⟩
    obtain ⟨Gamma,HG,w,hw,_hlen,_hbound,HQ,a,HA,hx⟩:=
      FormulaSignSlotRadialJointStratumLabels.component_hit (FormulaSignSlotRadialJointStratum.packet H k) x HB
    exact of_sampled_point H k Gamma w HG hw HQ a hx HA

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderJointWitnessGeometry
