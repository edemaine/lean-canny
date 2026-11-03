/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalPrefixSampler
public import LeanCanny.Encoding.IntegralMixedRoadmapVertexBudget
/-! # One original word-width budget for every positive padded-root prefix

The record table, final probe, cap and width are fixed BEFORE any word is
chosen. The bound covers each prefix's own complete sampler; it transports
no vertex ordinal between distinct prefixes or distinct prepared roots.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapWidth
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapRecordChain
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
 (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R : List Bool→ℕ} (hR : BinaryFn R)

noncomputable def prefixContextBudget (original : List Bool):=
 contextBudget hn ht ha original+cap (dimension (n:=n) original) (initial (n:=n) original)+1

theorem prefixContextBudget_unary : UnaryFn (prefixContextBudget hn ht ha):=
 ((contextBudget_unary hn ht ha).add (cap_unary (hn.add (UnaryFn.const 3)) (hn.add (UnaryFn.const 8)))).add
   (UnaryFn.const 1)

attribute [local irreducible] contextBudget tableBudget candidateBudget recordBudget scalarBudget prefixContextBudget

theorem padded_prefix_context_length (original label : List Bool)
    (hlabel : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {labels : ℕ} (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) (b : ℕ)
    (hb : b≤cap (dimension (n:=n) original) (initial (n:=n) original)+1) :
    (IntegralMixedPhysicalPrefixSampler.packet (records.root seed probe (pair original label) []) b).length≤
      prefixContextBudget hn ht ha original:=by
 have HR:=padded_root_length hn ht ha original label hlabel records seed probe
 simp only [IntegralMixedPhysicalPrefixSampler.packet,pair_length,List.length_replicate]
 unfold prefixContextBudget contextBudget at *
 omega

theorem actual_padded_cap (original label : List Bool) {labels : ℕ}
    (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) :
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters.cap
      (records.root seed probe (pair original label) [])=
        cap (dimension (n:=n) original) (initial (n:=n) original):=by
 change (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR).cap _=_
 rw [certified_cap hn ht ha hR,padded_cap hn ht ha original label records seed probe]

theorem padded_prefix_key (original label : List Bool) {labels : ℕ}
    (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) (b : ℕ) (hb : 0<b)
    (hc : b≤cap (dimension (n:=n) original) (initial (n:=n) original)+1) :
    IntegralMixedPhysicalPrefixSampler.key (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
      (IntegralMixedPhysicalPrefixSampler.packet (records.root seed probe (pair original label) []) b)=
        IntegralMixedFramedHistoryFamilyBits.keyAt (records.root seed probe (pair original label) []) b []:=by
 apply IntegralMixedPhysicalPrefixSampler.key_packet _ _ b hb
 rw [actual_padded_cap hn ht ha hR]
 exact hc

theorem exists_prefixVertexBudget : ∃ W : List Bool→ℕ,UnaryFn W ∧
    ∀original label,label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original→
      ∀(labels : ℕ)(records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
        (seed probe : Word (recordBudget hn ht ha original)) (b : ℕ),
        b≤cap (dimension (n:=n) original) (initial (n:=n) original)+1→
        SquareSampleCompleteVertices.width (IntegralMixedPhysicalPrefixSampler.input hn ht ha hR false)
          (IntegralMixedPhysicalPrefixSampler.packet (records.root seed probe (pair original label) []) b)≤W original:=by
 obtain ⟨W,hW,hbound⟩:=(IntegralMixedPhysicalPrefixSampler.width_unary hn ht ha hR false).wordEnvelope
   (prefixContextBudget_unary hn ht ha)
 refine ⟨W,hW,?_⟩
 intro original label hlabel labels records seed probe b hb
 exact hbound original _ (padded_prefix_context_length hn ht ha original label hlabel records seed probe b hb)

noncomputable def prefixVertexBudget : List Bool→ℕ:=Classical.choose (exists_prefixVertexBudget hn ht ha hR)
theorem prefixVertexBudget_unary : UnaryFn (prefixVertexBudget hn ht ha hR):=
 (Classical.choose_spec (exists_prefixVertexBudget hn ht ha hR)).1

theorem width_le_prefixVertexBudget (original label : List Bool)
    (hlabel : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {labels : ℕ} (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) (b : ℕ)
    (hb : b≤cap (dimension (n:=n) original) (initial (n:=n) original)+1) :
    SquareSampleCompleteVertices.width (IntegralMixedPhysicalPrefixSampler.input hn ht ha hR false)
      (IntegralMixedPhysicalPrefixSampler.packet (records.root seed probe (pair original label) []) b)≤
        prefixVertexBudget hn ht ha hR original:=
 (Classical.choose_spec (exists_prefixVertexBudget hn ht ha hR)).2 original label hlabel labels records seed probe b hb

theorem atPrefix_width_le_prefixVertexBudget (original label : List Bool)
    (hlabel : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {labels : ℕ} (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) (b : ℕ) (hb : 0<b)
    (hc : b≤cap (dimension (n:=n) original) (initial (n:=n) original)+1) (u : List Bool) :
    let hfixed : b≤(IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters.cap
        (records.root seed probe (pair original label) [])+1:=by rw [actual_padded_cap hn ht ha hR];exact hc
    SquareSampleCompleteVertices.width (IntegralMixedPhysicalPrefixSampler.atPrefix hn ht ha hR false
      (records.root seed probe (pair original label) []) b hb hfixed) u≤prefixVertexBudget hn ht ha hR original:=by
 dsimp only
 rw [IntegralMixedPhysicalPrefixSampler.width_packet]
 exact width_le_prefixVertexBudget hn ht ha hR original label hlabel records seed probe b hc

theorem word_length_le_prefixVertexBudget (original label : List Bool)
    (hlabel : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {labels : ℕ} (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) (b : ℕ)
    (hb : b≤cap (dimension (n:=n) original) (initial (n:=n) original)+1) (word : List Bool)
    (hword : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalPrefixSampler.input hn ht ha hR false)
      (IntegralMixedPhysicalPrefixSampler.packet (records.root seed probe (pair original label) []) b) word) :
    word.length≤prefixVertexBudget hn ht ha hR original:=
 (Classical.choose hword).1.le.trans (width_le_prefixVertexBudget hn ht ha hR original label hlabel records seed probe b hb)

theorem prefixVertexBudget_polynomial : ∃p : Polynomial ℕ,∀original,
    prefixVertexBudget hn ht ha hR original≤p.eval original.length:=by
 obtain ⟨p,hp⟩:=output_length_poly_of_mem_FP (prefixVertexBudget_unary hn ht ha hR).mem_FP
 exact ⟨p,fun original=>by simpa only [List.length_replicate] using hp original⟩

end LeanCanny.Encoding.IntegralMixedRoadmapWidth
