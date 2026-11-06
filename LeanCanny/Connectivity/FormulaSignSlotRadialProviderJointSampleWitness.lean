/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderJointWitnessGeometry
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderGuardedJointWitness
/-! # Exact native certificates retain a prescribed jointly labelled own point -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderJointSampleWitness
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open FormulaSignSlotRadialProviderJointWitness
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "OB" => FormulaSignSlotRadialProviderOriginalBudget.vertexBudget
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
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

private theorem seed_pair_lengths (H : List Bool) (k : ℕ) (Gamma w : List Bool) (side : Bool) (a e : List Bool)
    (hGamma : Gamma.length≤FormulaSignSlotRadialJointStratumSampler.tableBound (FormulaSignSlotRadialJointStratum.packet H k))
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialJointStratumSampler.input
      (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w)
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language)
    (hg : AuxiliaryCandidateComponentCover.Good CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope
      (FormulaSignSlotRadialJointLayout.source side H) (label side H))
    (hs : SeedPair H k Gamma w side a e) : a.length≤OB H ∧e.length≤OB H := by
  have HA:=(FormulaSignSlotRadialProviderAnchoredAssociation.language_iff a e).mp hs.2.2
  have HVa : FormulaSignSlotRadialProviderAtomic.Valid a := by
    simpa only [FormulaSignSlotRadialProviderAssociation.Guards,FormulaSignSlotRadialProviderAssociation.left,pairFst_pair]
      using HA.1.1.1
  have HVe : FormulaSignSlotRadialProviderAtomic.Valid e := by
    simpa only [FormulaSignSlotRadialProviderAssociation.Guards,FormulaSignSlotRadialProviderAssociation.right,pairSnd_pair]
      using HA.1.1.2.1
  have HB:=FormulaSignSlotRadialProviderOriginalBudget.provider_vertex_budgets H k Gamma (label side H) side w hGamma hw hq hg
  have HBa:=FormulaSignSlotRadialProviderAtomic.vertex_length_provider a HVa
  have HBe:=FormulaSignSlotRadialProviderAtomic.vertex_length_provider e HVe
  rw [hs.1] at HBa
  rw [hs.2.1] at HBe
  exact ⟨HBa.trans HB.2,HBe.trans HB.1⟩

/-- Honest native encoding completeness for actual seed pairs. The accepted
association tests are inputs here; their geometric construction is separate.
All table, sampler-word and seed size allowances are derived internally. -/
theorem witness_of_seed_pairs (H : List Bool) (k : ℕ) (Gamma w aL eL aR eR : List Bool)
    (hGamma : Gamma.length≤FormulaSignSlotRadialJointStratumSampler.tableBound (FormulaSignSlotRadialJointStratum.packet H k))
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language)
    (hg : ∀side,AuxiliaryCandidateComponentCover.Good CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope
      (FormulaSignSlotRadialJointLayout.source side H) (label side H))
    (hL : SeedPair H k Gamma w false aL eL) (hR : SeedPair H k Gamma w true aR eR) : Witness H k Gamma w aL eL aR eR := by
  have hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialJointStratumSampler.input
      (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w := by
    simpa only [pairFst_pair,pairSnd_pair] using hq.1
  have HK:=FormulaSignSlotRadialProviderOriginalBudget.selected_le _ w hw hq
  simp only [ImplicitSourceGramGrid.header,FormulaSignSlotRadialJointStratum.packet,
    FormulaSignSlotRadialJointStratum.selected,FormulaSignSlotRadialJointStratum.header,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] at HK
  have HU:=FormulaSignSlotRadialProviderOriginalBudget.stratum_length H k HK
  have HT : FormulaSignSlotRadialJointStratumSampler.tableBound (FormulaSignSlotRadialJointStratum.packet H k)≤
      FormulaSignSlotRadialProviderOriginalBudget.tableBudget H :=
    (Classical.choose_spec FormulaSignSlotRadialProviderOriginalBudget.table_exists).2 H _ HU
  have HW : FormulaSignSlotRadialJointStratumSampler.ownwordBound (FormulaSignSlotRadialJointStratum.packet H k)≤
      FormulaSignSlotRadialProviderOriginalBudget.ownwordBudget H :=
    (Classical.choose_spec FormulaSignSlotRadialProviderOriginalBudget.word_exists).2 H _ HU
  have HW0:=(Classical.choose hw).1
  have HW1:=ImplicitSourceGramGridWordBudget.width_le FormulaSignSlotRadialJointStratum.source
    FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive
    (FormulaSignSlotRadialJointStratum.packet H k) Gamma hGamma
  have HL:=seed_pair_lengths H k Gamma w false aL eL hGamma hw hq (hg false) hL
  have HR:=seed_pair_lengths H k Gamma w true aR eR hGamma hw hq (hg true) hR
  exact ⟨⟨HK,hGamma.trans HT,HW0.le.trans (HW1.trans HW),HL.1,HL.2,HR.1,HR.2⟩,hGamma,hq,hL,hR⟩

theorem witness_of_sampled_point (H:List Bool) (k:ℕ) (Gamma w:List Bool)
    (hGamma:Gamma.length≤FormulaSignSlotRadialJointStratumSampler.tableBound (FormulaSignSlotRadialJointStratum.packet H k))
    (hw:SquareSampleCompleteVertices.Valid F (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w)
    (hq:pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language)
    (x:FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H k))
    (hx:HEq (SquareSampleCompleteVertices.candidate F (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w hw).val x.val)
    (HB:FormulaSignSlotRadialJointStratumLabels.BothLabels (FormulaSignSlotRadialJointStratum.packet H k) x):
    ∃aL eL aR eR:List Bool,Witness H k Gamma w aL eL aR eR:=by
  obtain ⟨aL,eL,_haL,_heL,HLa,HLe,_hdL,_hdeL,HL⟩:=
    (FormulaSignSlotRadialProviderStratumLabelGeometry.atLabel_iff_exists_anchored_pair H k Gamma false w hw hq x hx).mp (HB false)
  obtain ⟨aR,eR,_haR,_heR,HRa,HRe,_hdR,_hdeR,HR⟩:=
    (FormulaSignSlotRadialProviderStratumLabelGeometry.atLabel_iff_exists_anchored_pair H k Gamma true w hw hq x hx).mp (HB true)
  refine ⟨aL,eL,aR,eR,witness_of_seed_pairs H k Gamma w aL eL aR eR hGamma hq ?_ ?_ ?_⟩
  · intro side
    have HG:=(HB side).choose
    exact (good_packet H k side).mp HG
  · exact ⟨by simpa only [label_packet] using HLa,by simpa only [label_packet] using HLe,HL⟩
  · exact ⟨by simpa only [label_packet] using HRa,by simpa only [label_packet] using HRe,HR⟩

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderJointSampleWitness
