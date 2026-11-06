/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicSize
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderPair
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumLabels
/-! # Original joint-header budgets for the literal paired provider graphs

The table-size receipt belongs to the actual bounded component sampler.
Acceptance alone imposes no bound on arbitrary unused metadata padding.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderOriginalBudget
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialJointStratum.source
local notation "F" => FormulaSignSlotRadialJointCoefficientCatalogue.family
local notation "I" => FormulaSignSlotRadialJointStratumSampler.input
local notation "hn" => CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht" => CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha" => CanonicalAuxiliaryCandidateCover.equation_scope

noncomputable def featureCount (H : List Bool) := (F).count H
theorem featureCount_binary : BinaryFn featureCount :=
  FormulaSignSlotRadialJointCoefficientCatalogue.access.count

/-- The real reciprocal-square certificate bounds the selected binary index. -/
theorem selected_le (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid I c w)
    (h : pair c w∈FormulaSignSlotRadialJointStratumSampler.language) :
    FormulaSignSlotRadialJointStratum.selected (ImplicitSourceGramGrid.header c)≤
      featureCount (FormulaSignSlotRadialJointStratum.header (ImplicitSourceGramGrid.header c)) := by
  have HC := ((FormulaSignSlotRadialJointStratumSampler.accepted_iff c w hw).mp h).2
  have HE := (SquareFeatureProduct.exists_certificate_iff _ _).mp ⟨_,HC⟩
  have HB := SquareFeatureProduct.zeroCount_le
    (FormulaSignSlotRadialJointStratum.values (ImplicitSourceGramGrid.header c)
      (SquareSampleCompleteVertices.candidate I c w hw).val)
  rw [HE] at HB
  simpa only [FormulaSignSlotRadialJointStratum.values,SquareFeatureProductEvaluation.values,
    List.length_ofFn,featureCount] using HB

noncomputable def stratumBound (H : List Bool) := 2*H.length+(featureCount H).size+2
theorem stratumBound_unary : UnaryFn stratumBound := by
  have HS : UnaryFn (fun H=>(featureCount H).size) :=
    (UnaryFn.length featureCount_binary.bits_mem_FP).of_eq (fun H=>BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add HS).add (UnaryFn.const 2)

theorem stratum_length (H : List Bool) (k : ℕ) (hk : k≤featureCount H) :
    (FormulaSignSlotRadialJointStratum.packet H k).length≤stratumBound H := by
  simp only [FormulaSignSlotRadialJointStratum.packet,pair_length,BinaryNatCode.length_encode,stratumBound]
  have HS:=Nat.size_le_size hk
  omega

theorem table_exists : ∃B : List Bool→ℕ,UnaryFn B ∧∀H u,u.length≤stratumBound H→
    FormulaSignSlotRadialJointStratumSampler.tableBound u≤B H :=
  FormulaSignSlotRadialJointStratumSampler.tableBound_unary.wordEnvelope stratumBound_unary
noncomputable def tableBudget : List Bool→ℕ := Classical.choose table_exists
theorem tableBudget_unary : UnaryFn tableBudget := (Classical.choose_spec table_exists).1
private theorem tableBudget_le (H u : List Bool) (hu : u.length≤stratumBound H) :
    FormulaSignSlotRadialJointStratumSampler.tableBound u≤tableBudget H :=
  (Classical.choose_spec table_exists).2 H u hu

theorem word_exists : ∃B : List Bool→ℕ,UnaryFn B ∧∀H u,u.length≤stratumBound H→
    FormulaSignSlotRadialJointStratumSampler.ownwordBound u≤B H :=
  FormulaSignSlotRadialJointStratumSampler.ownwordBound_unary.wordEnvelope stratumBound_unary
noncomputable def ownwordBudget : List Bool→ℕ := Classical.choose word_exists
theorem ownwordBudget_unary : UnaryFn ownwordBudget := (Classical.choose_spec word_exists).1
private theorem ownwordBudget_le (H u : List Bool) (hu : u.length≤stratumBound H) :
    FormulaSignSlotRadialJointStratumSampler.ownwordBound u≤ownwordBudget H :=
  (Classical.choose_spec word_exists).2 H u hu

noncomputable def sourceBudget (H : List Bool) := max
  (FormulaSignSlotRadialJointLayout.source false H).length (FormulaSignSlotRadialJointLayout.source true H).length
theorem sourceBudget_unary : UnaryFn sourceBudget :=
  (UnaryFn.length (FormulaSignSlotRadialJointLayout.source_FP false)).max
    (UnaryFn.length (FormulaSignSlotRadialJointLayout.source_FP true))
private theorem sourceBudget_le (side : Bool) (H : List Bool) :
    (FormulaSignSlotRadialJointLayout.source side H).length≤sourceBudget H := by
  cases side
  · exact le_max_left _ _
  · exact le_max_right _ _

noncomputable def labelBudget (H : List Bool) := max
  (IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (FormulaSignSlotRadialJointLayout.source false H))
  (IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (FormulaSignSlotRadialJointLayout.source true H))
theorem labelBudget_unary : UnaryFn labelBudget :=
  ((IntegralMixedAuxiliaryCandidate.labelWidth_unary hn ht ha).comp
    (FormulaSignSlotRadialJointLayout.source_FP false)).max
  ((IntegralMixedAuxiliaryCandidate.labelWidth_unary hn ht ha).comp
    (FormulaSignSlotRadialJointLayout.source_FP true))
private theorem labelBudget_le (H label : List Bool) (side : Bool)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha (FormulaSignSlotRadialJointLayout.source side H) label) :
    label.length≤labelBudget H := by
  have HL := hg.choose.1.1
  simp only [pairFst_pair,pairSnd_pair] at HL
  rw [HL]
  cases side
  · exact le_max_left _ _
  · exact le_max_right _ _

noncomputable def providerBound (H : List Bool) :=
  4*sourceBudget H+2*labelBudget H+4*stratumBound H+2*tableBudget H+ownwordBudget H+20
theorem providerBound_unary : UnaryFn providerBound :=
  ((((((UnaryFn.const 4).mul sourceBudget_unary).add ((UnaryFn.const 2).mul labelBudget_unary)).add
    ((UnaryFn.const 4).mul stratumBound_unary)).add ((UnaryFn.const 2).mul tableBudget_unary)).add
      ownwordBudget_unary).add (UnaryFn.const 20)

theorem vertex_exists : ∃B : List Bool→ℕ,UnaryFn B ∧∀H c,c.length≤providerBound H→
    FormulaSignSlotRadialProviderAtomic.providerVertexBudget c≤B H :=
  FormulaSignSlotRadialProviderAtomic.providerVertexBudget_unary.wordEnvelope providerBound_unary
noncomputable def vertexBudget : List Bool→ℕ := Classical.choose vertex_exists
theorem vertexBudget_unary : UnaryFn vertexBudget := (Classical.choose_spec vertex_exists).1
private theorem vertexBudget_le (H c : List Bool) (hc : c.length≤providerBound H) :
    FormulaSignSlotRadialProviderAtomic.providerVertexBudget c≤vertexBudget H :=
  (Classical.choose_spec vertex_exists).2 H c hc

private theorem packet_length (H : List Bool) (k : ℕ) (Gamma label : List Bool) (side : Bool) (w : List Bool) :
    (FormulaSignSlotRadialExternalContext.packet H k Gamma label side w).length=
      4*(FormulaSignSlotRadialJointLayout.source side H).length+2*label.length+
        4*(FormulaSignSlotRadialJointStratum.packet H k).length+2*Gamma.length+w.length+20 := by
  simp only [FormulaSignSlotRadialExternalContext.packet,pair_length,List.length_cons,List.length_nil]
  omega

private theorem oldOf_length (H : List Bool) (k : ℕ) (Gamma label : List Bool) (side : Bool) (w : List Bool) :
    (FormulaSignSlotRadialProviderPair.oldOf (FormulaSignSlotRadialExternalContext.packet H k Gamma label side w)).length=
      (FormulaSignSlotRadialExternalContext.packet H k Gamma label side w).length := by
  simp only [FormulaSignSlotRadialProviderPair.oldOf,FormulaSignSlotRadialExternalContext.packet,
    pairFst_pair,pairSnd_pair,pair_length,List.length_cons,List.length_nil]

/-- Both literal providers have an original-header bound, using the actual
sampler's table-size certificate and no bound supplied for its own word. -/
theorem provider_lengths (H : List Bool) (k : ℕ) (Gamma label : List Bool) (side : Bool) (w : List Bool)
    (hGamma : Gamma.length≤FormulaSignSlotRadialJointStratumSampler.tableBound
      (FormulaSignSlotRadialJointStratum.packet H k))
    (hw : SquareSampleCompleteVertices.Valid I (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w)
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha (FormulaSignSlotRadialJointLayout.source side H) label) :
    (FormulaSignSlotRadialExternalContext.packet H k Gamma label side w).length≤providerBound H ∧
    (FormulaSignSlotRadialProviderPair.oldOf (FormulaSignSlotRadialExternalContext.packet H k Gamma label side w)).length≤
      providerBound H := by
  have HK := selected_le _ w hw hq
  simp only [ImplicitSourceGramGrid.header,FormulaSignSlotRadialJointStratum.packet,
    FormulaSignSlotRadialJointStratum.selected,FormulaSignSlotRadialJointStratum.header,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] at HK
  have HU := stratum_length H k HK
  have HG := hGamma.trans (tableBudget_le H _ HU)
  have HW0 := (Classical.choose hw).1
  have HW1 := ImplicitSourceGramGridWordBudget.width_le S FormulaSignSlotRadialJointStratumNative.access
    FormulaSignSlotRadialJointStratumSampler.positive (FormulaSignSlotRadialJointStratum.packet H k) Gamma hGamma
  have HW : w.length≤ownwordBudget H := HW0.le.trans (HW1.trans (ownwordBudget_le H _ HU))
  have HS := sourceBudget_le side H
  have HL := labelBudget_le H label side hg
  have HB : (FormulaSignSlotRadialExternalContext.packet H k Gamma label side w).length≤providerBound H := by
    rw [packet_length]
    unfold providerBound
    omega
  exact ⟨HB,by rw [oldOf_length];exact HB⟩

theorem provider_vertex_budgets (H : List Bool) (k : ℕ) (Gamma label : List Bool) (side : Bool) (w : List Bool)
    (hGamma : Gamma.length≤FormulaSignSlotRadialJointStratumSampler.tableBound
      (FormulaSignSlotRadialJointStratum.packet H k))
    (hw : SquareSampleCompleteVertices.Valid I (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w)
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha (FormulaSignSlotRadialJointLayout.source side H) label) :
    FormulaSignSlotRadialProviderAtomic.providerVertexBudget
      (FormulaSignSlotRadialExternalContext.packet H k Gamma label side w)≤vertexBudget H ∧
    FormulaSignSlotRadialProviderAtomic.providerVertexBudget
      (FormulaSignSlotRadialProviderPair.oldOf (FormulaSignSlotRadialExternalContext.packet H k Gamma label side w))≤vertexBudget H := by
  have HB := provider_lengths H k Gamma label side w hGamma hw hq hg
  exact ⟨vertexBudget_le H _ HB.1,vertexBudget_le H _ HB.2⟩

theorem vertex_length (H : List Bool) (k : ℕ) (Gamma label : List Bool) (side : Bool) (w q : List Bool)
    (hGamma : Gamma.length≤FormulaSignSlotRadialJointStratumSampler.tableBound
      (FormulaSignSlotRadialJointStratum.packet H k))
    (hw : SquareSampleCompleteVertices.Valid I (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w)
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language)
    (hg : AuxiliaryCandidateComponentCover.Good hn ht ha (FormulaSignSlotRadialJointLayout.source side H) label)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hp : FormulaSignSlotRadialProviderAtomic.provider q=FormulaSignSlotRadialExternalContext.packet H k Gamma label side w ∨
      FormulaSignSlotRadialProviderAtomic.provider q=FormulaSignSlotRadialProviderPair.oldOf
        (FormulaSignSlotRadialExternalContext.packet H k Gamma label side w)) : q.length≤vertexBudget H := by
  have HB := provider_vertex_budgets H k Gamma label side w hGamma hw hq hg
  have HV := FormulaSignSlotRadialProviderAtomic.vertex_length_provider q hv
  rcases hp with hp|hp
  · rw [hp] at HV
    exact HV.trans HB.1
  · rw [hp] at HV
    exact HV.trans HB.2


/-- The original component sampler itself supplies every metadata-size receipt.
The same chosen grid word meets both prescribed labels and bounds both literal
provider graphs by one unary function of the original joint header. -/
theorem component_hit_bounded_providers (H : List Bool) (k : ℕ)
    (x : FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H k))
    (hx : FormulaSignSlotRadialJointStratumLabels.BothLabels (FormulaSignSlotRadialJointStratum.packet H k) x) :
    ∃Gamma : List Bool,Gamma.length≤tableBudget H ∧
      ∃(w : List Bool) (hw : SquareSampleCompleteVertices.Valid I
        (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w),
        w.length≤ownwordBudget H ∧
        pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w∈FormulaSignSlotRadialJointStratumSampler.language ∧
        (∃a : FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H k),
          FormulaSignSlotRadialJointStratumLabels.BothLabels (FormulaSignSlotRadialJointStratum.packet H k) a ∧
          HEq (SquareSampleCompleteVertices.candidate I
            (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w hw).val a.val) ∧
        ∀side : Bool,
          let label:=FormulaSignSlotRadialJointStratumLabels.label side (FormulaSignSlotRadialJointStratum.packet H k)
          let ext:=FormulaSignSlotRadialExternalContext.packet H k Gamma label side w
          FormulaSignSlotRadialProviderAtomic.providerVertexBudget ext≤vertexBudget H ∧
          FormulaSignSlotRadialProviderAtomic.providerVertexBudget (FormulaSignSlotRadialProviderPair.oldOf ext)≤vertexBudget H ∧
          ∀q,FormulaSignSlotRadialProviderAtomic.Valid q→
            (FormulaSignSlotRadialProviderAtomic.provider q=ext ∨
              FormulaSignSlotRadialProviderAtomic.provider q=FormulaSignSlotRadialProviderPair.oldOf ext)→
            q.length≤vertexBudget H := by
  obtain ⟨Gamma,hGamma,w,hw,hlen,_,hq,a,hLabels,hpoint⟩:=
    FormulaSignSlotRadialJointStratumLabels.component_hit (FormulaSignSlotRadialJointStratum.packet H k) x hx
  have HK:=selected_le _ w hw hq
  simp only [ImplicitSourceGramGrid.header,FormulaSignSlotRadialJointStratum.packet,
    FormulaSignSlotRadialJointStratum.selected,FormulaSignSlotRadialJointStratum.header,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] at HK
  have HU:=stratum_length H k HK
  have HW1:=ImplicitSourceGramGridWordBudget.width_le S FormulaSignSlotRadialJointStratumNative.access
    FormulaSignSlotRadialJointStratumSampler.positive (FormulaSignSlotRadialJointStratum.packet H k) Gamma hGamma
  refine ⟨Gamma,hGamma.trans (tableBudget_le H _ HU),w,hw,
    hlen.le.trans (HW1.trans (ownwordBudget_le H _ HU)),hq,⟨a,hLabels,hpoint⟩,?_⟩
  intro side
  dsimp only
  have HG:=Classical.choose (hx side)
  have HGood : AuxiliaryCandidateComponentCover.Good hn ht ha (FormulaSignSlotRadialJointLayout.source side H)
      (FormulaSignSlotRadialJointStratumLabels.label side (FormulaSignSlotRadialJointStratum.packet H k)) := by
    simpa only [FormulaSignSlotRadialJointStratumLabels.Good,FormulaSignSlotRadialJointStratumLabels.source,
      FormulaSignSlotRadialJointStratum.header,FormulaSignSlotRadialJointStratum.packet,pairFst_pair] using HG
  have HB:=provider_vertex_budgets H k Gamma _ side w hGamma hw hq HGood
  exact ⟨HB.1,HB.2,fun q hv hp=>vertex_length H k Gamma _ side w q hGamma hw hq HGood hv hp⟩

theorem vertexBudget_polynomial : ∃p : Polynomial ℕ,∀H,vertexBudget H≤p.eval H.length := by
  obtain ⟨p,hp⟩:=output_length_poly_of_mem_FP vertexBudget_unary.mem_FP
  exact ⟨p,fun H=>by simpa only [List.length_replicate] using hp H⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderOriginalBudget
