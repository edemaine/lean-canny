/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderJointWitnessLayout
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderAnchoredAssociation
/-! # Native original-header search with one shared stratum sample -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderJointWitness
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "OB" => FormulaSignSlotRadialProviderOriginalBudget.vertexBudget

noncomputable def Sizes (H : List Bool) (k : ℕ) (Gamma w aL eL aR eR : List Bool) : Prop :=
  k≤FormulaSignSlotRadialProviderOriginalBudget.featureCount H ∧
  Gamma.length≤FormulaSignSlotRadialProviderOriginalBudget.tableBudget H ∧
  w.length≤FormulaSignSlotRadialProviderOriginalBudget.ownwordBudget H ∧
  aL.length≤OB H ∧eL.length≤OB H ∧aR.length≤OB H ∧eR.length≤OB H

noncomputable def SeedPair (H : List Bool) (k : ℕ) (Gamma w : List Bool) (side : Bool) (a e : List Bool) : Prop :=
  let ext:=FormulaSignSlotRadialExternalContext.packet H k Gamma (label side H) side w
  FormulaSignSlotRadialProviderAtomic.provider a=FormulaSignSlotRadialProviderPair.oldOf ext ∧
  FormulaSignSlotRadialProviderAtomic.provider e=ext ∧
  pair a e∈FormulaSignSlotRadialProviderAnchoredAssociation.language

noncomputable def Witness (H : List Bool) (k : ℕ) (Gamma w aL eL aR eR : List Bool) : Prop :=
  Sizes H k Gamma w aL eL aR eR ∧
  Gamma.length≤FormulaSignSlotRadialJointStratumSampler.tableBound (FormulaSignSlotRadialJointStratum.packet H k) ∧
  pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language ∧
  SeedPair H k Gamma w false aL eL ∧SeedPair H k Gamma w true aR eR

private theorem length_le_FP (f : List Bool→List Bool) (hf : f∈FP) (b : List Bool→ℕ) (hb : UnaryFn b) :
    FPPred (fun q=>(f q).length≤b (header q)) :=
  (BinaryFn.ofUnary (UnaryFn.length hf)).le (BinaryFn.ofUnary (hb.comp header_FP))

noncomputable def sizesInput (q : List Bool) := Sizes (header q) (kind q) (gamma q) (ownWord q)
  (oldSeed false q) (externalSeed false q) (oldSeed true q) (externalSeed true q)
theorem sizesInput_FP : FPPred sizesInput :=
  (kind_binary.le (FormulaSignSlotRadialProviderOriginalBudget.featureCount_binary.comp header_FP)).and
    ((length_le_FP gamma gamma_FP _ FormulaSignSlotRadialProviderOriginalBudget.tableBudget_unary).and
    ((length_le_FP ownWord ownWord_FP _ FormulaSignSlotRadialProviderOriginalBudget.ownwordBudget_unary).and
    ((length_le_FP (oldSeed false) (oldSeed_FP false) _ FormulaSignSlotRadialProviderOriginalBudget.vertexBudget_unary).and
    ((length_le_FP (externalSeed false) (externalSeed_FP false) _ FormulaSignSlotRadialProviderOriginalBudget.vertexBudget_unary).and
    ((length_le_FP (oldSeed true) (oldSeed_FP true) _ FormulaSignSlotRadialProviderOriginalBudget.vertexBudget_unary).and
      (length_le_FP (externalSeed true) (externalSeed_FP true) _ FormulaSignSlotRadialProviderOriginalBudget.vertexBudget_unary))))))

noncomputable def actualTableFit (q : List Bool) :=
  (gamma q).length≤FormulaSignSlotRadialJointStratumSampler.tableBound (stratum q)
theorem actualTableFit_FP : FPPred actualTableFit :=
  (BinaryFn.ofUnary (UnaryFn.length gamma_FP)).le
    (BinaryFn.ofUnary (FormulaSignSlotRadialJointStratumSampler.tableBound_unary.comp stratum_FP))

noncomputable def providersMatch (side : Bool) (q : List Bool) :=
  FormulaSignSlotRadialProviderAtomic.provider (oldSeed side q)=oldProvider side q ∧
  FormulaSignSlotRadialProviderAtomic.provider (externalSeed side q)=externalProvider side q
theorem providersMatch_FP (side : Bool) : FPPred (providersMatch side) :=
  (Brackets.stringEq_fppred (mem_FP_comp (oldSeed_FP side) FormulaSignSlotRadialProviderAtomic.provider_FP)
    (oldProvider_FP side)).and
  (Brackets.stringEq_fppred (mem_FP_comp (externalSeed_FP side) FormulaSignSlotRadialProviderAtomic.provider_FP)
    (externalProvider_FP side))

def associationQuery (side : Bool) (q : List Bool) :=pair (oldSeed side q) (externalSeed side q)
theorem associationQuery_FP (side : Bool) : associationQuery side∈FP :=
  mem_FP_pair (oldSeed_FP side) (externalSeed_FP side)

noncomputable def rawLanguage : Language := {q |Witness (header q) (kind q) (gamma q) (ownWord q)
  (oldSeed false q) (externalSeed false q) (oldSeed true q) (externalSeed true q)}

theorem raw_decider : SpaceDecider rawLanguage := by
  have EB:=SpaceFunction.ofFP _ sizesInput_FP.flag_mem_FP
  have ET:=SpaceFunction.ofFP _ actualTableFit_FP.flag_mem_FP
  have EP (s : Bool):=SpaceFunction.ofFP _ (providersMatch_FP s).flag_mem_FP
  have ES:=(ImplicitSourceComponentSampler.decider FormulaSignSlotRadialJointStratum.source
    FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive).precompose
    sampleQuery sampleQuery_FP
  have EA (s : Bool):=(FormulaSignSlotRadialProviderAnchoredAssociation.decider.precompose
    (associationQuery s) (associationQuery_FP s)).flagEvaluator
  apply (EB.andFlags (ET.andFlags (ES.flagEvaluator.andFlags
    ((EP false).andFlags ((EA false).andFlags ((EP true).andFlags (EA true))))))).decider
    (fun v=>decide (v=[true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [rawLanguage,Witness,Sizes,sizesInput,actualTableFit,SeedPair,providersMatch,oldProvider,
    externalProvider,sampleQuery,stratum,associationQuery,Set.mem_ofPred_eq,Set.mem_preimage,
    List.cons.injEq,and_true,decide_eq_true_eq]
  tauto

def probe (q : List Bool) :=pair (pairFst q) (IntegralMixedRoadmapWordLabel.decode (pairSnd q))
theorem probe_FP : probe∈FP := mem_FP_pair pairFst_mem_FP
  (mem_FP_comp pairSnd_mem_FP IntegralMixedRoadmapWordLabel.decode_FP)
noncomputable def Bounded (H : List Bool) : Prop :=∃bits : List Bool,bits.length=width H ∧probe (pair H bits)∈rawLanguage
noncomputable def language : Language := {H |Bounded H}

theorem bounded_evaluator : SpaceFunction (fun H=>[decide (Bounded H)]) := by
  have E:=(raw_decider.precompose probe probe_FP).flagEvaluator.exists_words width_unary
  exact E.congr (funext fun H=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Bounded,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq])
theorem decider : SpaceDecider language := by
  apply bounded_evaluator.decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro H
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE : language∈PSPACE := decider.mem_PSPACE


theorem raw_packet_iff (H : List Bool) (k : ℕ) (Gamma w aL eL aR eR : List Bool) :
    packet H k Gamma w aL eL aR eR∈rawLanguage ↔Witness H k Gamma w aL eL aR eR := by
  obtain ⟨HH,HK,HG,HW,HL,HR⟩:=packet_readers H k Gamma w aL eL aR eR
  simp only [rawLanguage,Set.mem_ofPred_eq,HH,HK,HG,HW,oldSeed,externalSeed,HL,HR,pairFst_pair,pairSnd_pair]

/-- This is an exact bounded native-witness characterization. Both sides use
one and the same stratum kind, witness table and complete sampler word. -/
theorem language_iff (H : List Bool) : H∈language ↔
    ∃k : ℕ,∃Gamma w aL eL aR eR : List Bool,Witness H k Gamma w aL eL aR eR := by
  change (∃bits : List Bool,bits.length=width H ∧probe (pair H bits)∈rawLanguage)↔_
  constructor
  · rintro ⟨bits,_,HL⟩
    let z:=probe (pair H bits)
    have HH : header z=H := by simp only [header,z,probe,pairFst_pair]
    have HZ : Witness (header z) (kind z) (gamma z) (ownWord z)
        (oldSeed false z) (externalSeed false z) (oldSeed true z) (externalSeed true z) := HL
    exact ⟨kind z,gamma z,ownWord z,oldSeed false z,externalSeed false z,oldSeed true z,externalSeed true z,
      by simpa only [HH] using HZ⟩
  · rintro ⟨k,Gamma,w,aL,eL,aR,eR,HW⟩
    have HB : (data (packet H k Gamma w aL eL aR eR)).length≤rawBudget H := by
      obtain ⟨HK,HG,HWd,HA,HE,HA',HE'⟩:=HW.1
      exact packet_length H k Gamma w aL eL aR eR HK HG HWd HA HE HA' HE'
    let bits:=IntegralMixedRoadmapWordLabel.encode (rawBudget H) (data (packet H k Gamma w aL eL aR eR))
    refine ⟨bits,IntegralMixedRoadmapWordLabel.encode_length _ _ HB,?_⟩
    have HE : probe (pair H bits)=packet H k Gamma w aL eL aR eR := by
      simp only [probe,pairFst_pair,pairSnd_pair,bits,IntegralMixedRoadmapWordLabel.decode_encode,data,packet]
    rw [HE]
    exact (raw_packet_iff H k Gamma w aL eL aR eR).mpr HW


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
theorem of_seed_pairs (H : List Bool) (k : ℕ) (Gamma w aL eL aR eR : List Bool)
    (hGamma : Gamma.length≤FormulaSignSlotRadialJointStratumSampler.tableBound (FormulaSignSlotRadialJointStratum.packet H k))
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language)
    (hg : ∀side,AuxiliaryCandidateComponentCover.Good CanonicalAuxiliaryCandidateCover.dimension_unary
      CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope
      (FormulaSignSlotRadialJointLayout.source side H) (label side H))
    (hL : SeedPair H k Gamma w false aL eL) (hR : SeedPair H k Gamma w true aR eR) : H∈language := by
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
  exact (language_iff H).mpr ⟨k,Gamma,w,aL,eL,aR,eR,
    ⟨⟨HK,hGamma.trans HT,HW0.le.trans (HW1.trans HW),HL.1,HL.2,HR.1,HR.2⟩,hGamma,hq,hL,hR⟩⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderJointWitness
