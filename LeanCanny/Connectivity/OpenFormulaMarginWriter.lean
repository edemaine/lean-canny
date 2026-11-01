/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.OpenFormulaMarginHomeomorph
public import LeanCanny.Connectivity.ClosedFormulaGateLanguages
public import LeanCanny.Encoding.MonotoneGateNativeBounds
/-! # Native actual-input single-equation reduction and one initial budget for strict-positive Boolean formulas -/
@[expose] public section
namespace LeanCanny.Connectivity.OpenFormulaMarginValues
open ETR Set LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.query
  OpenFormulaGateMetadata.atom OpenFormulaGateMetadata.kind

noncomputable def prepared (c : List Bool) : List Bool := (Input.whole (PositiveMarginSource.description F c)).encode

theorem prepared_FP : prepared ∈ FP := PositiveMarginSource.whole_record_FP F OpenFormulaGateMetadata.access

noncomputable def writer (c : List Bool) : List Bool := ClosedFormulaGateTruth.wholeWriter (prepared c)

theorem writer_FP : writer ∈ FP := mem_FP_comp prepared_FP ClosedFormulaGateTruth.wholeWriter_FP

noncomputable def polynomial (c : List Bool) : Term := MonotoneGateSource.polynomial ClosedFormulaGateMetadata.family (prepared c)

theorem polynomial_FP : (fun c => (polynomial c).toData.toBits) ∈ FP :=
  mem_FP_comp prepared_FP ClosedFormulaGateMetadata.source_FP

noncomputable def dimensionBudget (c : List Bool) : ℕ :=
  (MonotoneGateGraph.description ClosedFormulaGateMetadata.family (prepared c)).dimension

theorem dimensionBudget_unary : UnaryFn dimensionBudget :=
  (MonotoneGateGraph.description_dim_unary ClosedFormulaGateMetadata.family ClosedFormulaGateMetadata.access).comp prepared_FP

noncomputable def degreeBudget (c : List Bool) : ℕ := MonotoneGateSource.degreeBudget ClosedFormulaGateMetadata.family (prepared c)

theorem degreeBudget_unary : UnaryFn degreeBudget :=
  (MonotoneGateSource.degreeBudget_unary ClosedFormulaGateMetadata.family ClosedFormulaGateMetadata.access).comp prepared_FP

theorem polynomial_degree (c : List Bool) : (polynomial c).toPolynomial.totalDegree≤degreeBudget c :=
  MonotoneGateSource.polynomial_totalDegree_budget _ _

theorem language_iff {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c) :
    writer c∈connectedLanguage ↔ (Input.whole (Description.mk (ClosedFormulaGateMetadata.dimension c) p)).encode∈connectedLanguage := by
  unfold writer prepared
  rw [ClosedFormulaGateTruth.canonical_whole_language_iff _ (PositiveMarginSource.source_closed F c)
    (PositiveMarginSource.description_wellFormed F c (source_scope c))]
  simpa only [whole_encode_mem_iff] using connected_iff hp c hc hs

theorem dimension_whole (d : Description) : ClosedFormulaGateMetadata.dimension (Input.whole d).encode=d.dimension := by
  unfold ClosedFormulaGateMetadata.dimension
  rw [Input.field_whole_dimension,Codec.unaryValue_toBits]

theorem canonical_language_iff (d : Description) (hp : OpenFormulaMargin.Open d.formula) (hd : d.WellFormed) :
    writer (Input.whole d).encode∈connectedLanguage ↔ (Input.whole d).encode∈connectedLanguage := by
  have HC : FormulaView.normalize (Input.field 2 (Input.whole d).encode)=d.formula.encode := by
    rw [Input.field_whole_space,FormulaView.normalize_encode]
  have HS : d.formula.arity≤ClosedFormulaGateMetadata.dimension (Input.whole d).encode := by rw [dimension_whole]; exact hd
  have H:=language_iff hp (Input.whole d).encode HC HS
  have HE : Description.mk (ClosedFormulaGateMetadata.dimension (Input.whole d).encode) d.formula=d := by rw [dimension_whole]
  rw [HE] at H
  exact H

end LeanCanny.Connectivity.OpenFormulaMarginValues
