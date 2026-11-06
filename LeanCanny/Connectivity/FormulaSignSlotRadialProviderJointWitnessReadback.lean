/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderJointSampleWitness
public import LeanCanny.Connectivity.FormulaSignSlotRadialImplicitSampleReadback
/-! # A native certificate retains its exact sampled point and both labels -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderJointWitnessReadback
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open CoerciveComponentSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
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


theorem point_of_witness (H : List Bool) (k : ℕ) (Gamma w aL eL aR eR : List Bool)
    (h : FormulaSignSlotRadialProviderJointWitness.Witness H k Gamma w aL eL aR eR) :
    ∃ hw : SquareSampleCompleteVertices.Valid F (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w,
    ∃ x : FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H k),
      FormulaSignSlotRadialJointStratumLabels.BothLabels (FormulaSignSlotRadialJointStratum.packet H k) x ∧
      HEq (SquareSampleCompleteVertices.candidate F (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w hw).val x.val := by
  have HQ := h.2.2.1
  obtain ⟨hw,x,hx⟩ := sampled_zero FormulaSignSlotRadialJointStratum.source
    FormulaSignSlotRadialJointStratumSampler.positive (FormulaSignSlotRadialJointStratum.packet H k)
    (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w (pairFst_pair _ _) HQ
  refine ⟨hw,x,?_,hx⟩
  intro side
  cases side
  · exact seed_pair_atLabel H k Gamma w hw HQ x hx false aL eL h.2.2.2.1
  · exact seed_pair_atLabel H k Gamma w hw HQ x hx true aR eR h.2.2.2.2

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderJointWitnessReadback
