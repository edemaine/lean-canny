/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicLayout
public import LeanCanny.Encoding.IntegralMixedRoadmapChainMetadataSize
/-! # Checked atomic syntax uses the actual provider record parameters

The scalar metadata allowance is the actual provider width. This syntax
check does not assume that an external point has an old candidate label.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialProviderIntegerSource.degreeBound

noncomputable def dimension (q : List Bool) :=
  FormulaSignSlotRadialProviderRecordPlan.parameters.ambient (root q)
noncomputable def initial (q : List Bool) := FormulaSignSlotRadialProviderRecordPlan.count (root q)
noncomputable def width (q : List Bool) := FormulaSignSlotRadialProviderRecordPlan.parameters.width (root q)
noncomputable def sourceCap (q : List Bool) := IntegralMixedExceptionalBounds.auxiliaryCap
  (dimension q+1) (FormulaSignSlotRadialProviderRecordPlan.parameters.degree (root q))

theorem dimension_unary : UnaryFn dimension := FormulaSignSlotRadialProviderRecordPlan.access.ambient.comp root_FP
theorem initial_unary : UnaryFn initial := FormulaSignSlotRadialProviderRecordPlan.count_unary.comp root_FP
theorem width_unary : UnaryFn width := FormulaSignSlotRadialProviderRecordPlan.access.width.comp root_FP
theorem sourceCap_binary : BinaryFn sourceCap :=
  IntegralMixedExceptionalBounds.auxiliaryCap_binary (dimension_unary.add (UnaryFn.const 1))
    (FormulaSignSlotRadialProviderRecordPlan.access.degree.comp root_FP)

theorem dimension_provider (q : List Bool) :
    dimension q=FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient (provider q) := by
  change FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (root q))=_
  rw [root_provider]
theorem width_provider (q : List Bool) :
    width q=FormulaSignSlotRadialProviderIntegerPlan.parameters.width (provider q) := by
  unfold width FormulaSignSlotRadialProviderRecordPlan.parameters
    FormulaSignSlotRadialProviderRecordPlan.degreeBound
    FormulaSignSlotRadialProviderIntegerPlan.parameters
    IntegralMixedSourceIntegerPrelude.parameters IntegralMixedSourceIntegerPrelude.ceiling
  simp only [Function.comp_apply,root_provider]
theorem initial_eq (q : List Bool) : initial q=dimension q+5 := by
  rw [dimension_provider]
  change FormulaSignSlotRadialProviderIntegerPlan.count
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (root q))=_
  rw [root_provider]
  change FormulaSignSlotRadialProviderIntegerPlan.number (provider q)+8=
    FormulaSignSlotRadialProviderIntegerPlan.number (provider q)+3+5
  omega
theorem sourceCap_le (q : List Bool) : sourceCap q≤2^width q :=
  FormulaSignSlotRadialProviderRecordPlan.spatial_cap (root q)
private theorem source_at_heq {n : List Bool → ℕ} (F : (c : List Bool) → IntegralMixedHistory.SpatialSource (n c))
    (c d : List Bool) (h : c=d) : HEq (F c) (F d) := by cases h; rfl
theorem spatial_provider (q : List Bool) : HEq (FormulaSignSlotRadialProviderRecordPlan.spatial (root q))
    (FormulaSignSlotRadialProviderIntegerPlan.spatial (provider q)) := by
  unfold FormulaSignSlotRadialProviderRecordPlan.spatial
  exact source_at_heq FormulaSignSlotRadialProviderIntegerPlan.spatial _ _ (root_provider q)

def Canonical (q : List Bool) := q=packet (provider q) (payload q) (word q)
theorem canonical_FP : FPPred Canonical := Brackets.stringEq_fppred id_mem_FP
  (mem_FP_pair provider_FP (mem_FP_pair payload_FP word_FP))

noncomputable def CheckedGrammar (q : List Bool) := Canonical q ∧
  IntegralMixedRoadmapChain.Checked (dimension q) (width q) (sourceCap q) (initial q) (width q) (payload q)
theorem checkedGrammar_FP : FPPred CheckedGrammar := canonical_FP.and
  (IntegralMixedRoadmapChain.checkedAt_FP dimension_unary width_unary sourceCap_binary
    (BinaryFn.ofUnary initial_unary) width_unary payload_FP)

theorem checked (q : List Bool) (h : CheckedGrammar q) :
    IntegralMixedRoadmapChain.Checked (dimension q) (width q) (sourceCap q) (initial q) (width q) (payload q) := h.2
theorem depth_le (q : List Bool) (h : CheckedGrammar q) : depth q≤dimension q := h.2.1
theorem raw_count (q : List Bool) (h : CheckedGrammar q) :
    WordListRecords.count (IntegralMixedRoadmapChain.raw (payload q))=
      IntegralMixedRoadmapRecordChain.probedRecordBound (dimension q) := h.2.2.2.2.2.2.2.1
theorem full_count (q : List Bool) (h : CheckedGrammar q) :
    FormulaSignSlotRadialProviderRecordPlan.fullCount (root q)=
      initial q+IntegralMixedRoadmapRecordChain.probedRecordBound (dimension q) := by
  change initial q+IntegralMixedCausalRecordPlanBits.count (root q)=_
  rw [IntegralMixedCausalRecordPlanBits.count,root_records,raw_count q h]
theorem raw_length (q : List Bool) (h : CheckedGrammar q) :
    (IntegralMixedRoadmapChain.raw (payload q)).length≤
      (2*IntegralMixedRoadmapRecordChain.codeBound (dimension q) (initial q) (width q)+2)*
        IntegralMixedRoadmapRecordChain.probedRecordBound (dimension q) :=
  IntegralMixedRoadmapChain.raw_length_le h.2
theorem payload_length (q : List Bool) (h : CheckedGrammar q) : (payload q).length≤
    IntegralMixedRoadmapChain.payloadBudget (dimension q) (initial q) (width q) :=
  IntegralMixedRoadmapChain.payload_length h.2

theorem native_companionQuery : (fun q => companionQuery (dimension q) (initial q) q) ∈ FP :=
  companionQuery_FP dimension_unary initial_unary
theorem native_signature : (fun q => signature (dimension q) (initial q) q) ∈ FP :=
  signature_FP dimension_unary initial_unary

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
