/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicSample
public import LeanCanny.Encoding.IntegralFramedPhysicalLeafSources
public import LeanCanny.Encoding.IntegralMixedMarkedPointTest
/-! # Actual provider integer leaves and the two marked equations

The integer source is the literal provider record source. Spatial marked
terms read the retained provider context, including for external points.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.Marked
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open FormulaSignSlotRadialProviderAtomic (input input_access row_evaluator bank_represents)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "A" => FormulaSignSlotRadialProviderRecordPlan.bank_access
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "hn" => CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht" => CanonicalAuxiliaryCandidateCover.equation_FP
local notation "n" => CanonicalAuxiliaryCandidateCover.dimension
local notation "t" => CanonicalAuxiliaryCandidateCover.equation
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderRecordPlan.tables

noncomputable def leafSource := IntegralFramedPhysicalLeafSources.source FormulaSignSlotRadialProviderRecordPlan.source
theorem leafSource_access : IntegerPolynomialRootQueriesBits.Access leafSource :=
  IntegralFramedPhysicalLeafSources.source_access _ FormulaSignSlotRadialProviderRecordPlan.source_access
noncomputable def leafCount (c : List Bool) := FormulaSignSlotRadialProviderRecordPlan.count (pairFst c)
theorem leafCount_unary : UnaryFn leafCount := FormulaSignSlotRadialProviderRecordPlan.count_unary.comp pairFst_mem_FP
attribute [local irreducible] leafSource leafCount
noncomputable def leafLanguage := IntegralFramedPhysicalIntegerLeaves.language (B).parameters (B).plan (B).data
  (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive leafSource leafCount
theorem leaves_decider : SpaceDecider leafLanguage :=
  IntegralFramedPhysicalIntegerLeaves.decider (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive leafSource leafCount
    (A).parameters T FormulaSignSlotRadialProviderRecordPlan.tables_native bank_represents (A).liftedData
    (A).controls (A).bounds (A).nodes (A).factor (A).seed (A).key leafSource_access leafCount_unary row_evaluator

noncomputable def regularWord := IntegralMixedMarkedPointTest.regularWord n t ∘FormulaSignSlotRadialProviderRecordPlan.providerContext
noncomputable def markWord := IntegralMixedMarkedPointTest.markWord n t ∘FormulaSignSlotRadialProviderRecordPlan.providerContext
theorem regularWord_FP : regularWord∈FP := mem_FP_comp
  FormulaSignSlotRadialProviderRecordPlan.providerContext_FP (IntegralMixedMarkedPointTest.regularWord_FP hn ht)
theorem markWord_FP : markWord∈FP := mem_FP_comp
  FormulaSignSlotRadialProviderRecordPlan.providerContext_FP (IntegralMixedMarkedPointTest.markWord_FP hn ht)
def probe (q : List Bool) := pair (FormulaSignSlotRadialProviderAtomic.sampleQuery q) []
theorem probe_FP : probe∈FP := mem_FP_pair FormulaSignSlotRadialProviderAtomic.sampleQuery_FP (constFn_mem_FP [])
noncomputable def regularValue := IntegralFramedPhysicalBankTerm.value B T bank_represents regularWord ∘probe
noncomputable def markValue := IntegralFramedPhysicalBankTerm.value B T bank_represents markWord ∘probe
theorem regular_evaluator : SpaceFunction regularValue :=
  (IntegralFramedPhysicalBankTerm.evaluator B T bank_represents A
    FormulaSignSlotRadialProviderRecordPlan.tables_native regularWord regularWord_FP row_evaluator).precompose probe probe_FP
theorem mark_evaluator : SpaceFunction markValue :=
  (IntegralFramedPhysicalBankTerm.evaluator B T bank_represents A
    FormulaSignSlotRadialProviderRecordPlan.tables_native markWord markWord_FP row_evaluator).precompose probe probe_FP
attribute [local irreducible] regularValue markValue leafLanguage

noncomputable def Holds (q : List Bool) := FormulaSignSlotRadialProviderAtomic.sampleQuery q∈leafLanguage ∧
  regularValue q=InfinitesimalSign.encode 0 ∧ markValue q=InfinitesimalSign.encode 0
theorem decider : SpaceDecider {q | Holds q} := by
  have EL := (leaves_decider.precompose FormulaSignSlotRadialProviderAtomic.sampleQuery
    FormulaSignSlotRadialProviderAtomic.sampleQuery_FP).flagEvaluator
  have ER := regular_evaluator.postcompose (fun z => [decide (z=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have EM := mark_evaluator.postcompose (fun z => [decide (z=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  apply (EL.andFlags (ER.andFlags EM)).decider (fun z => decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [Holds,Set.mem_ofPred_eq,Set.mem_preimage,Function.comp_apply,
    List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE : {q | Holds q}∈PSPACE := decider.mem_PSPACE

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.Marked
