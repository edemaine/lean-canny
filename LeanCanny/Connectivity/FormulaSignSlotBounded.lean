/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotLabels
public import LeanCanny.Encoding.BoundedMonotoneGateNativeBounds
public import LeanCanny.Connectivity.ClosedFormulaBoundedGate
/-! # Native bounded equation sources for every fixed-width original-formula sign label

This compiles the closed weak envelope. Selection by the original Boolean
truth and strict stratum remains a separate validity/geometry step.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotBounded
open ETR LeanCanny.Computation LeanCanny.Encoding
open scoped Classical
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension
  ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom ClosedFormulaGateMetadata.kind

noncomputable def prepared (c : List Bool) : List Bool := (Input.whole (FormulaSignSlotSource.description c)).encode
noncomputable def writer (c : List Bool) : List Bool := ClosedFormulaBoundedGate.writer (prepared c)

attribute [local irreducible] prepared

theorem prepared_FP : prepared ∈ FP := by
  unfold prepared
  exact FormulaSignSlotSource.whole_record_FP
theorem writer_FP : writer ∈ FP := by
  unfold writer
  exact mem_FP_comp (f := prepared) (g := ClosedFormulaBoundedGate.writer) prepared_FP ClosedFormulaBoundedGate.writer_FP

theorem language_iff (c : List Bool) : writer c∈connectedLanguage ↔
    (Input.whole (FormulaSignSlotSource.description c)).encode∈connectedLanguage := by
  unfold writer prepared
  exact ClosedFormulaBoundedGate.canonical_language_iff (FormulaSignSlotSource.description c)
    (FormulaSignSlotSource.envelope_closed c) (FormulaSignSlotSource.description_wellFormed c)

noncomputable def polynomial (c : List Bool) : Term :=
  BoundedMonotoneGateSource.polynomial ClosedFormulaGateTruth.F (prepared c)
noncomputable def dimensionBudget (c : List Bool) : ℕ :=
  BoundedMonotoneGateSource.total ClosedFormulaGateTruth.F (prepared c)
noncomputable def degreeBudget (c : List Bool) : ℕ :=
  BoundedMonotoneGateSource.degreeBudget ClosedFormulaGateTruth.F (prepared c)

theorem polynomial_FP : (fun c => (polynomial c).toData.toBits) ∈ FP := by
  unfold polynomial
  exact mem_FP_comp (f := prepared)
    (g := fun c => (BoundedMonotoneGateSource.polynomial ClosedFormulaGateTruth.F c).toData.toBits)
    prepared_FP (BoundedMonotoneGateSource.polynomial_FP _ ClosedFormulaGateMetadata.access)
theorem dimensionBudget_unary : UnaryFn dimensionBudget := by
  unfold dimensionBudget
  exact UnaryFn.comp (f := BoundedMonotoneGateSource.total ClosedFormulaGateTruth.F)
    (g := prepared) (BoundedMonotoneGateSource.total_unary _ ClosedFormulaGateMetadata.access) prepared_FP
theorem degreeBudget_unary : UnaryFn degreeBudget := by
  unfold degreeBudget
  exact UnaryFn.comp (f := BoundedMonotoneGateSource.degreeBudget ClosedFormulaGateTruth.F)
    (g := prepared) (BoundedMonotoneGateSource.degreeBudget_unary _ ClosedFormulaGateMetadata.access) prepared_FP

theorem polynomial_degree (c : List Bool) : (polynomial c).toPolynomial.totalDegree≤degreeBudget c := by
  unfold polynomial degreeBudget
  exact BoundedMonotoneGateSource.polynomial_totalDegree_budget ClosedFormulaGateTruth.F (prepared c)

theorem polynomial_arity (c : List Bool) : (polynomial c).arity≤dimensionBudget c := by
  unfold polynomial dimensionBudget
  exact BoundedMonotoneGateSource.polynomial_arity ClosedFormulaGateTruth.F (prepared c)
    (ClosedFormulaGateTruth.source_scope (prepared c))

end LeanCanny.Connectivity.FormulaSignSlotBounded
