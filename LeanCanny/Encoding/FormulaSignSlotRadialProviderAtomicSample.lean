/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicGrammar
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordNative
public import LeanCanny.Encoding.IntegralFramedPhysicalSquareNative
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermPoint
/-! # One actual provider full sampler and its provider-only word budget

Native row access is derived from the concrete record factory. Every
sample refers to the literal record context and its separate own word.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.certifiedCallerControls
  FormulaSignSlotRadialProviderRecordPlan.tables

noncomputable abbrev input := IntegralFramedPhysicalBankTerm.input FormulaSignSlotRadialProviderRecordPlan.bank

theorem bank_represents : IntegralMixedFramedHeaderBits.Represents
    FormulaSignSlotRadialProviderRecordPlan.bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank.plan
    FormulaSignSlotRadialProviderRecordPlan.bank.data FormulaSignSlotRadialProviderRecordPlan.tables := by
  unfold FormulaSignSlotRadialProviderRecordPlan.bank
  exact FormulaSignSlotRadialProviderRecordPlan.certifiedRepresents

private theorem bank_row_evaluator (B : IntegralFramedBankQuery.Bank) (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) :
    SpaceFunction (SquareSampleInput.rowCoefficient (IntegralFramedPhysicalBankTerm.input B)) := by
  exact IntegralFramedPhysicalSquare.native_row_evaluator B.parameters A.parameters B.plan B.data
    T hT hr B.nodes B.factor B.seed B.bounds B.key A.key B.positive A.liftedData A.controls A.bounds

private theorem bank_input_access (B : IntegralFramedBankQuery.Bank) (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) :
    (IntegralFramedPhysicalBankTerm.input B).Access := by
  exact IntegralFramedPhysicalSquare.native_access B.parameters A.parameters B.plan B.data
    T hT hr B.nodes B.factor B.seed B.bounds A.nodes A.factor
    A.seed B.key A.key B.positive A.liftedData A.controls A.bounds

theorem row_evaluator : SpaceFunction (SquareSampleInput.rowCoefficient input) :=
  bank_row_evaluator FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.bank_access
    FormulaSignSlotRadialProviderRecordPlan.tables FormulaSignSlotRadialProviderRecordPlan.tables_native bank_represents
theorem input_access : input.Access :=
  bank_input_access FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.bank_access
    FormulaSignSlotRadialProviderRecordPlan.tables FormulaSignSlotRadialProviderRecordPlan.tables_native bank_represents

noncomputable def FullValid (q : List Bool) := SquareSampleCompleteVertices.Valid input (context q) (word q)
theorem full_decider : SpaceDecider {q | FullValid q} := by
  have E := (SquareSampleCompleteVertices.decider input_access).precompose sampleQuery sampleQuery_FP
  convert E using 1
  ext q
  simp only [FullValid,sampleQuery,Set.mem_preimage,SquareSampleCompleteVertices.language,
    pairFst_pair,pairSnd_pair,Set.mem_ofPred_eq]

noncomputable def providerRawBudget (c : List Bool) :=
  (2*IntegralMixedRoadmapRecordChain.codeBound
      (FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient c)
      (FormulaSignSlotRadialProviderIntegerPlan.count c)
      (FormulaSignSlotRadialProviderIntegerPlan.parameters.width c)+2)*
    IntegralMixedRoadmapRecordChain.probedRecordBound (FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient c)
theorem providerRawBudget_unary : UnaryFn providerRawBudget := by
  have HC := IntegralMixedRoadmapRecordChain.codeBound_unary
    FormulaSignSlotRadialProviderIntegerPlan.access.ambient
    (BinaryFn.ofUnary FormulaSignSlotRadialProviderIntegerPlan.count_unary)
    FormulaSignSlotRadialProviderIntegerPlan.access.width
  exact (((UnaryFn.const 2).mul HC).add (UnaryFn.const 2)).mul
    ((IntegralMixedRoadmapRecordChain.recordBound_unary
      FormulaSignSlotRadialProviderIntegerPlan.access.ambient).add (UnaryFn.const 1))

theorem initial_provider (q : List Bool) : initial q=FormulaSignSlotRadialProviderIntegerPlan.count (provider q) := by
  unfold initial FormulaSignSlotRadialProviderRecordPlan.count
  rw [root_provider]
theorem raw_length_provider (q : List Bool) (h : CheckedGrammar q) :
    (IntegralMixedRoadmapChain.raw (payload q)).length≤providerRawBudget (provider q) := by
  simpa only [providerRawBudget,dimension_provider,initial_provider,width_provider] using raw_length q h

noncomputable def providerContextBudget (c : List Bool) := 4*c.length+4*providerRawBudget c+10
theorem providerContextBudget_unary : UnaryFn providerContextBudget :=
  (((UnaryFn.const 4).mul (UnaryFn.length id_mem_FP)).add
    ((UnaryFn.const 4).mul providerRawBudget_unary)).add (UnaryFn.const 10)
theorem context_length_provider (q : List Bool) (h : CheckedGrammar q) :
    (context q).length≤providerContextBudget (provider q) := by
  have HR := raw_length_provider q h
  simp only [context,root,FormulaSignSlotRadialProviderRecordPlan.root,pair_length,List.length_nil]
  unfold providerContextBudget
  omega

theorem exists_providerWordBudget : ∃ B : List Bool → ℕ, UnaryFn B ∧
    ∀ c ctx, ctx.length≤providerContextBudget c → SquareSampleCompleteVertices.width input ctx≤B c :=
  (SquareSampleCompleteVertices.width_unary input_access).wordEnvelope providerContextBudget_unary
noncomputable def providerWordBudget := Classical.choose exists_providerWordBudget
theorem providerWordBudget_unary : UnaryFn providerWordBudget :=
  (Classical.choose_spec exists_providerWordBudget).1
theorem full_width_le (q : List Bool) (h : CheckedGrammar q) :
    SquareSampleCompleteVertices.width input (context q)≤providerWordBudget (provider q) :=
  (Classical.choose_spec exists_providerWordBudget).2 _ _ (context_length_provider q h)
theorem word_length_le (q : List Bool) (h : CheckedGrammar q) (hv : FullValid q) :
    (word q).length≤providerWordBudget (provider q) := by
  obtain ⟨hw,_⟩ := hv
  exact hw.1.le.trans (full_width_le q h)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
