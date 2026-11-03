/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapWidthSnapshot
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedNative
/-! # Original-only budgets for full physical roadmap sample words

The original candidate, padded record table, and empty metadata field give
one original-only bound for the actual sampler context. The complete-width
reader then supplies one unary budget and a polynomial majorant. This does
not transport words between prepared roots or assert record realizability.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapWidth
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapRecordChain
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem Records.root_length {d T labels : ℕ} (records : Records d T labels) (seed probe : Word T)
    (candidate metadata : List Bool) :
    (records.root seed probe candidate metadata).length≤
      2*candidate.length+4+2*((2*T+2)*probedRecordBound d)+metadata.length :=by
  have HU:=records.paddedWord_length seed probe
  simp only [IntegralMixedRoadmapRecordChain.Records.root,pair_length]
  omega

theorem Records.context_length {d T labels : ℕ} (records : Records d T labels) (seed probe : Word T)
    (candidate metadata : List Bool) :
    (pair (records.root seed probe candidate metadata) []).length≤
      4*candidate.length+4*((2*T+2)*probedRecordBound d)+2*metadata.length+10 :=by
  have HU:=Records.root_length records seed probe candidate metadata
  simp only [pair_length,List.length_nil]
  omega

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)

def dimension (original : List Bool) :=n original+3
def initial (original : List Bool) :=n original+8
noncomputable def recordBudget (original : List Bool) :=
  codeBound (dimension (n:=n) original) (initial (n:=n) original) (scalarBudget hn ht ha original)
noncomputable def tableBudget (original : List Bool) :=
  (2*recordBudget hn ht ha original+2)*probedRecordBound (dimension (n:=n) original)
noncomputable def contextBudget (original : List Bool) :=
  4*candidateBudget hn ht ha original+4*tableBudget hn ht ha original+10

theorem recordBudget_unary : UnaryFn (recordBudget hn ht ha) :=
  codeBound_unary (hn.add (UnaryFn.const 3)) (BinaryFn.ofUnary (hn.add (UnaryFn.const 8)))
    (scalarBudget_unary hn ht ha)

theorem tableBudget_unary : UnaryFn (tableBudget hn ht ha) :=
  probedWordBound_unary (hn.add (UnaryFn.const 3)) (BinaryFn.ofUnary (hn.add (UnaryFn.const 8)))
    (scalarBudget_unary hn ht ha)

theorem contextBudget_unary : UnaryFn (contextBudget hn ht ha) :=
  (((UnaryFn.const 4).mul (candidateBudget_unary hn ht ha)).add
    ((UnaryFn.const 4).mul (tableBudget_unary hn ht ha))).add (UnaryFn.const 10)

attribute [local irreducible] scalarBudget recordBudget tableBudget candidateBudget contextBudget

theorem padded_context_length (original label : List Bool)
    (hlabel : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {labels : ℕ} (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) :
    (pair (records.root seed probe (pair original label) []) []).length≤contextBudget hn ht ha original :=by
  have HC:=candidate_length hn ht ha original label hlabel
  have HR:=Records.context_length records seed probe (pair original label) []
  simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at HR
  unfold contextBudget tableBudget
  omega

theorem padded_root_length (original label : List Bool)
    (hlabel : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {labels : ℕ} (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) :
    (records.root seed probe (pair original label) []).length≤
      2*candidateBudget hn ht ha original+4+2*tableBudget hn ht ha original :=by
  have HC:=candidate_length hn ht ha original label hlabel
  have HR:=Records.root_length records seed probe (pair original label) []
  simp only [List.length_nil,Nat.add_zero] at HR
  unfold tableBudget
  omega

theorem contextBudget_polynomial : ∃ p : Polynomial ℕ, ∀ original,
    contextBudget hn ht ha original≤p.eval original.length :=by
  obtain ⟨p,hp⟩:=output_length_poly_of_mem_FP (contextBudget_unary hn ht ha).mem_FP
  exact ⟨p,fun original=>by simpa only [List.length_replicate] using hp original⟩

theorem padded_scalar_width (original label : List Bool)
    (hlabel : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {labels : ℕ} (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) :
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width
      (records.root seed probe (pair original label) [])≤scalarBudget hn ht ha original :=
  width_le_scalarBudget hn ht ha original label (pair (records.paddedWord seed probe) []) hlabel

theorem padded_cap (original label : List Bool) {labels : ℕ}
    (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) :
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap
      (records.root seed probe (pair original label) [])=
        cap (dimension (n:=n) original) (initial (n:=n) original) :=by
  simpa only [pairFst_pair,initial] using records.actual_marked_cap hn ht ha seed probe (pair original label) []

theorem cut_code_length (original label tail : List Bool)
    (hlabel : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {birth : ℕ} (hb : birth≤maxBirth (dimension (n:=n) original) (initial (n:=n) original))
    (d : IntegralMixedCutRecordConstructor.Data (dimension (n:=n) original) birth)
    (tag : IntegralMixedCausalRecordBits.Tag) (choice degree : ℕ)
    (hc : choice≤2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (pair (pair original label) tail))
    (hd : degree≤2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (pair (pair original label) tail)) :
    (d.code tag choice degree).length≤recordBudget hn ht ha original :=by
  have H:=Nat.pow_le_pow_right (by decide : 1≤2)
    (width_le_scalarBudget hn ht ha original label tail hlabel)
  unfold recordBudget
  exact IntegralMixedRoadmapRecordChain.cut_code_length hb d tag choice degree (hc.trans H) (hd.trans H)

variable {R : List Bool→ℕ} (hR : BinaryFn R)

attribute [local irreducible] IntegralMixedAuxiliaryMarkedRecordPlan.parameters

theorem certified_width (root : List Bool) :
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR).width root=
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width root :=by
  simp only [IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters,IntegralMixedFramedNormalizationBits.planned]

theorem certified_cap (root : List Bool) :
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR).cap root=
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap root :=by
  simp only [IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters,IntegralMixedFramedNormalizationBits.planned]

theorem exists_vertexBudget : ∃ W : List Bool→ℕ, UnaryFn W ∧
    ∀ original label, label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original →
      ∀ (labels : ℕ) (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
        (seed probe : Word (recordBudget hn ht ha original)),
      SquareSampleCompleteVertices.width (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
        (pair (records.root seed probe (pair original label) []) [])≤W original :=by
  obtain ⟨W,hW,hbound⟩:=
    (SquareSampleCompleteVertices.width_unary (IntegralMixedPhysicalMarkedNative.access hn ht ha hR false)).wordEnvelope
      (contextBudget_unary hn ht ha)
  refine ⟨W,hW,?_⟩
  intro original label hlabel labels records seed probe
  exact hbound original _ (padded_context_length hn ht ha original label hlabel records seed probe)

noncomputable def vertexBudget : List Bool→ℕ :=Classical.choose (exists_vertexBudget hn ht ha hR)

theorem vertexBudget_unary : UnaryFn (vertexBudget hn ht ha hR) :=
  (Classical.choose_spec (exists_vertexBudget hn ht ha hR)).1

theorem width_le_vertexBudget (original label : List Bool)
    (hlabel : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {labels : ℕ} (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) :
    SquareSampleCompleteVertices.width (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (pair (records.root seed probe (pair original label) []) [])≤vertexBudget hn ht ha hR original :=
  (Classical.choose_spec (exists_vertexBudget hn ht ha hR)).2 original label hlabel labels records seed probe

theorem word_length_le_vertexBudget (original label : List Bool)
    (hlabel : label.length≤IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)
    {labels : ℕ} (records : Records (dimension (n:=n) original) (recordBudget hn ht ha original) labels)
    (seed probe : Word (recordBudget hn ht ha original)) (word : List Bool)
    (hword : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (pair (records.root seed probe (pair original label) []) []) word) :
    word.length≤vertexBudget hn ht ha hR original :=by
  exact (Classical.choose hword).1.le.trans
    (width_le_vertexBudget hn ht ha hR original label hlabel records seed probe)

theorem vertexBudget_polynomial : ∃ p : Polynomial ℕ, ∀ original,
    vertexBudget hn ht ha hR original≤p.eval original.length :=by
  obtain ⟨p,hp⟩:=output_length_poly_of_mem_FP (vertexBudget_unary hn ht ha hR).mem_FP
  exact ⟨p,fun original=>by simpa only [List.length_replicate] using hp original⟩

end LeanCanny.Encoding.IntegralMixedRoadmapWidth
