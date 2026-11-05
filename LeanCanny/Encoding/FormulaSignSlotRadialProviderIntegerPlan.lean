/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerSource
public import LeanCanny.Algebra.IntegralMixedSourceIntegerSnapshot
/-! # The actual OLD or EXTERNAL marked integer plan retains n+8 births -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev number := FormulaSignSlotRadialExternalPrelude.number
abbrev original := FormulaSignSlotRadialExternalPrelude.original
noncomputable abbrev source := FormulaSignSlotRadialProviderIntegerSource.source
theorem source_access : IntegerPolynomialRootQueriesBits.Access source := FormulaSignSlotRadialProviderIntegerSource.access
theorem source_nonzero (q : List Bool) : source.polynomial q ≠ 0 := FormulaSignSlotRadialProviderIntegerSource.nonzero q
noncomputable abbrev degreeBound := FormulaSignSlotRadialProviderIntegerSource.degreeBound
noncomputable abbrev radius := FormulaSignSlotRadialExternalPrelude.radius
theorem radius_binary : BinaryFn radius := FormulaSignSlotRadialExternalPrelude.radius_binary
noncomputable def count (ctx : List Bool) := number ctx+8
theorem count_unary : UnaryFn count := FormulaSignSlotRadialExternalContext.number_unary.add (UnaryFn.const 8)

noncomputable def parameters := IntegralMixedSourceIntegerPrelude.parameters (fun c => number c+3)
  (IntegralMixedAuxiliaryMarkedIntegerPlan.degree LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation)
  degreeBound count
theorem access : Access parameters := IntegralMixedSourceIntegerPrelude.access
  (FormulaSignSlotRadialExternalContext.number_unary.add (UnaryFn.const 3))
  (IntegralMixedAuxiliaryMarkedIntegerPlan.degree_binary LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation_FP)
  FormulaSignSlotRadialProviderIntegerSource.degreeBound_binary count_unary

noncomputable abbrev spatial := FormulaSignSlotRadialExternalPrelude.spatial
theorem spatial_degree (ctx : List Bool) : (spatial ctx).degree = parameters.degree ctx :=
  FormulaSignSlotRadialExternalPrelude.spatial_degree ctx
theorem source_cap (ctx : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap (parameters.ambient ctx+1) (parameters.degree ctx) ≤ 2^parameters.width ctx :=
  IntegralMixedSourceIntegerPrelude.source_cap _ _ _ _ ctx
theorem source_degree_cap (ctx : List Bool) (i : ℕ) : source.degree (pair ctx (BinaryNatCode.encode i)) ≤ 2^parameters.width ctx := by
  have H := FormulaSignSlotRadialProviderIntegerSource.degree_le (pair ctx (BinaryNatCode.encode i))
  rw [pairFst_pair] at H
  exact H.trans (IntegralMixedSourceIntegerPrelude.bound_cap _ _ _ _ ctx)
theorem room (ctx : List Bool) : count ctx+2 ≤ parameters.cap ctx+1 := by
  change count ctx+2 ≤ count ctx+2+1
  omega
theorem ambient_positive (ctx : List Bool) : 0 < parameters.ambient ctx := by change 0 < number ctx+3; omega
theorem source_width (ctx : List Bool) : (parameters.degree ctx).size ≤ parameters.sourceWidth ctx := le_rfl

noncomputable def plan := IntegralMixedSourceIntegerPrelude.plan parameters spatial spatial_degree source_cap
  source count source_nonzero source_degree_cap room
noncomputable def data := IntegralMixedSourceIntegerPrelude.data parameters spatial spatial_degree source_cap
  source count source_nonzero source_degree_cap room ambient_positive source_width
noncomputable def tables := IntegralMixedSourceIntegerPrelude.tables parameters count
theorem tables_native : IntegralMixedHeaderTablesBits.Access tables :=
  IntegralMixedSourceIntegerPrelude.tables_native parameters access count_unary
theorem tables_represents : IntegralMixedFramedHeaderBits.Represents parameters plan data tables :=
  IntegralMixedSourceIntegerPrelude.tables_represents parameters spatial spatial_degree source_cap source count
    source_nonzero source_degree_cap room ambient_positive source_width
theorem instruction_source (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction parameters plan key).source = spatial (pairFst key) :=
  IntegralMixedSourceIntegerPrelude.instruction_source parameters spatial spatial_degree source_cap source count
    source_nonzero source_degree_cap room key

noncomputable abbrev readers := FormulaSignSlotRadialExternalPrelude.readers
theorem readers_native : readers.PolyTime := FormulaSignSlotRadialExternalPrelude.readers_native
noncomputable abbrev savedReaders := FormulaSignSlotRadialExternalPrelude.savedReaders
theorem savedReaders_native : savedReaders.PolyTime := FormulaSignSlotRadialExternalPrelude.savedReaders_native
private theorem source_comp (R : BoundedFullWriter.Readers) (f : List Bool → List Bool) (key : List Bool) :
    HEq (BoundedRegularLowModularTerm.source R (f key)) (BoundedRegularLowModularTerm.source (R.comp f) key) := HEq.rfl
theorem snapshot : BoundedRegularFramedOriginalBits.Snapshot parameters plan savedReaders where
  ambient _ := rfl
  source key := (heq_of_eq (instruction_source key)).trans (source_comp readers pairFst key)

theorem rules_length (ctx : List Bool) : (plan.rules ctx).length = number ctx+8 := by
  simp only [plan,IntegralMixedSourceIntegerPrelude.plan,IntegralMixedSourceIntegerPrelude.commands_length,count]

theorem spatial_eq (ctx : List Bool) : spatial ctx = IntegralMixedAuxiliaryMarkedIntegerPlan.spatial
    LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.dimension
    LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation radius ctx :=
  FormulaSignSlotRadialExternalPrelude.spatial_eq ctx

end LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerPlan
