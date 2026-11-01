/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ClosedFormulaGatePointWriter
public import LeanCanny.Connectivity.ClosedFormulaGateValidation
/-! # Canonical connectivity-language reductions for actual closed Boolean inputs -/
@[expose] public section
namespace LeanCanny.Connectivity.ClosedFormulaGateTruth
open ETR Set LeanCanny.Encoding LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom
  ClosedFormulaGateMetadata.kind

noncomputable def wholeWriter (c : List Bool) : List Bool := (Input.whole (MonotoneGateGraph.description F c)).encode

theorem wholeWriter_FP : wholeWriter ∈ FP := ClosedFormulaGateMetadata.whole_record_FP

theorem whole_language_iff {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c) :
    wholeWriter c∈connectedLanguage ↔
      (Input.whole (Description.mk (F.dimension c) p)).encode∈connectedLanguage := by
  simp only [wholeWriter,whole_encode_mem_iff]
  change (MonotoneGateGraph.description F c).Connected ↔ (Description.mk (ClosedFormulaGateMetadata.dimension c) p).Connected
  exact original_connected_iff hp c hc hs

theorem dimension_point (q : PointQuery) : F.dimension (Input.point q).encode=q.space.dimension := by
  simp only [F,ClosedFormulaGateMetadata.family,ClosedFormulaGateMetadata.dimension,
    Input.field_point_dimension,Codec.unaryValue_toBits]

theorem dimension_whole (d : Description) : F.dimension (Input.whole d).encode=d.dimension := by
  simp only [F,ClosedFormulaGateMetadata.family,ClosedFormulaGateMetadata.dimension,
    Input.field_whole_dimension,Codec.unaryValue_toBits]

theorem canonical_whole_language_iff (d : Description) (hp : ClosedFormulaWitness.Closed d.formula)
    (hd : d.WellFormed) : wholeWriter (Input.whole d).encode∈connectedLanguage ↔ (Input.whole d).encode∈connectedLanguage := by
  have HC : FormulaView.normalize (Input.field 2 (Input.whole d).encode)=d.formula.encode := by
    rw [Input.field_whole_space,FormulaView.normalize_encode]
  have HS : d.formula.arity≤F.dimension (Input.whole d).encode := by rw [dimension_whole]; exact hd
  have H := whole_language_iff hp (Input.whole d).encode HC HS
  have HE : Description.mk (F.dimension (Input.whole d).encode) d.formula=d := by
    rw [dimension_whole]
  rw [HE] at H
  exact H

theorem endpointField_point (k : ℕ) (q : PointQuery) (hk : k=3 ∨ k=4) :
    ClosedFormulaGatePointWriter.endpointField k (Input.point q).encode=if k=3 then q.source else q.target := by
  rcases hk with rfl | rfl
  · simp only [ClosedFormulaGatePointWriter.endpointField,Input.field_point_source,FormulaView.formula_encode,ite_true]
  · simp only [ClosedFormulaGatePointWriter.endpointField,Input.field_point_target,FormulaView.formula_encode,
      show (4 : ℕ)≠3 by decide,ite_false]

theorem canonical_point_language_guarded_iff (q : PointQuery)
    (hp : ClosedFormulaWitness.Closed q.space.formula) (hq : q.space.WellFormed) :
    (Input.point q).encode∈pointLanguage ↔
      (Input.point q).encode∈EndpointValidation.validEndpointLanguage ∧
      ClosedFormulaGatePointWriter.writer (Input.point q).encode∈pointLanguage := by
  have HC : FormulaView.normalize (Input.field 2 (Input.point q).encode)=q.space.formula.encode := by
    rw [Input.field_point_space,FormulaView.normalize_encode]
  have HS : q.space.formula.arity≤F.dimension (Input.point q).encode := by rw [dimension_point]; exact hq
  have H := point_language_guarded_iff hp (Input.point q).encode HC HS q.source q.target
  have HE : PointQuery.mk (Description.mk (F.dimension (Input.point q).encode) q.space.formula) q.source q.target=q := by
    rw [dimension_point]
  have H3 := endpointField_point 3 q (Or.inl rfl)
  have H4 := endpointField_point 4 q (Or.inr rfl)
  simp only [ite_true] at H3
  simp only [show (4 : ℕ)≠3 by decide,ite_false] at H4
  simpa only [HE,ClosedFormulaGatePointWriter.writer,H3,H4] using H

end LeanCanny.Connectivity.ClosedFormulaGateTruth
