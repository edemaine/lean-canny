/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicSample
public import LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
public import LeanCanny.Algebra.IntegralMixedFramedPlannedProbe
/-! # Source-aware creating-cut tests retain the actual provider full tuple -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.Cuts
open LeanCanny.Algebra LeanCanny.Computation
open FormulaSignSlotRadialProviderAtomic (input input_access row_evaluator bank_represents)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "A" => FormulaSignSlotRadialProviderRecordPlan.bank_access
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables

theorem key_context (c : List Bool) : (B).key c=(B).key (pair (pairFst c) []) := by
  unfold FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.bankKey
  simp only [pairFst_pair]
theorem factor_positive : ∀root,1≤(B).factor root := FormulaSignSlotRadialProviderRecordPlan.factor_positive
theorem fallback : ∀q, IntegralMixedFramedOriginalBounds.FallbackBounds (B).parameters (B).plan (B).data
    (B).nodes (B).seed q := FormulaSignSlotRadialProviderRecordPlan.certifiedBounds.fallback

noncomputable def probeControls := IntegralMixedFramedPlannedProbe.controls
  FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderRecordPlan.plan
  FormulaSignSlotRadialProviderRecordPlan.data (fun _=>3) FormulaSignSlotRadialProviderRecordPlan.factor
  FormulaSignSlotRadialProviderRecordPlan.seed FormulaSignSlotRadialProviderRecordPlan.certifiedCallerControls
theorem probeBounds : IntegralMixedFramedCurrentQNativeBits.Bounds
    (IntegralMixedFramedCutProbeTaskBits.parameters (B).parameters (B).nodes (B).factor (B).seed)
    (IntegralMixedFramedCutProbeTransportBits.plan (B).parameters (B).plan (B).nodes (B).factor (B).seed)
    (IntegralMixedFramedCutProbeTransportBits.data (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed)
    probeControls := IntegralMixedFramedPlannedProbe.bounds
  FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderRecordPlan.plan
  FormulaSignSlotRadialProviderRecordPlan.data (fun _=>3) FormulaSignSlotRadialProviderRecordPlan.factor
  FormulaSignSlotRadialProviderRecordPlan.seed FormulaSignSlotRadialProviderRecordPlan.certifiedCallerControls
  FormulaSignSlotRadialProviderRecordPlan.certifiedCallerBounds

noncomputable def source := IntegralFramedPhysicalTraceCutSource.source B key_context factor_positive fallback
theorem source_access : source.Access := IntegralFramedPhysicalTraceCutSource.source_access B key_context
  factor_positive fallback A probeControls probeBounds
noncomputable def value := IntegralFramedPhysicalSuffixTest.value B T bank_represents source
theorem value_evaluator : SpaceFunction value := IntegralFramedPhysicalTraceCutSource.evaluator B key_context
  factor_positive fallback A probeControls probeBounds T bank_represents
  FormulaSignSlotRadialProviderRecordPlan.tables_native row_evaluator

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.Cuts
