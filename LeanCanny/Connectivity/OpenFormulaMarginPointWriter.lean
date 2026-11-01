/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.OpenFormulaMarginValidation
public import LeanCanny.Connectivity.ClosedFormulaGateLanguages
/-! # Native point-query writers for the exact open margin endpoint extension -/
@[expose] public section
namespace LeanCanny.Connectivity.OpenFormulaMarginValues
open ETR Set LeanCanny.Encoding LeanCanny.Computation
open scoped Classical

theorem point_record_FP {s d : List Bool → Formula}
    (hs : (fun c => (s c).encode) ∈ FP) (hd : (fun c => (d c).encode) ∈ FP) :
    (fun c => (Input.point (pointQuery c (s c) (d c))).encode) ∈ FP := by
  have HN:=PositiveMarginSource.total_unary F OpenFormulaGateMetadata.access
  have HP:=PositiveMarginSource.source_FP F OpenFormulaGateMetadata.access
  have HS:=PositiveMarginSource.endpoint_FP F OpenFormulaGateMetadata.access hs
  have HD:=PositiveMarginSource.endpoint_FP F OpenFormulaGateMetadata.access hd
  have H:=mem_FP_comp (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
    (appendFn_mem_FP (constFn_mem_FP (Codec.unary 0).toBits) (Codec.unary_toBits_mem_FP HN)) HP) HS) HD) Brackets.wrap_mem_FP
  apply mem_FP_of_eq H
  intro c
  simp only [Function.comp_apply,Input.encode,Input.toData,Data.toBits_l,Brackets.wrap,List.map_cons,List.map_nil,
    List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc,pointQuery,PositiveMarginSource.description,Formula.encode]

noncomputable def preparedPoint (c : List Bool) : List Bool :=
  (Input.point (pointQuery c (ClosedFormulaGatePointWriter.endpointField 3 c) (ClosedFormulaGatePointWriter.endpointField 4 c))).encode

theorem preparedPoint_FP : preparedPoint ∈ FP :=
  point_record_FP (ClosedFormulaGatePointWriter.endpointField_FP 3) (ClosedFormulaGatePointWriter.endpointField_FP 4)

noncomputable def pointWriter (c : List Bool) : List Bool := ClosedFormulaGatePointWriter.writer (preparedPoint c)

theorem pointWriter_FP : pointWriter ∈ FP := mem_FP_comp preparedPoint_FP ClosedFormulaGatePointWriter.writer_FP

theorem point_language_equation_guarded_iff {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (s d : Formula) :
    (Input.point (PointQuery.mk (Description.mk (ClosedFormulaGateMetadata.dimension c) p) s d)).encode∈pointLanguage ↔
      (Input.point (PointQuery.mk (Description.mk (ClosedFormulaGateMetadata.dimension c) p) s d)).encode∈EndpointValidation.validEndpointLanguage ∧
        ClosedFormulaGatePointWriter.writer (Input.point (pointQuery c s d)).encode∈pointLanguage := by
  have H1:=point_language_guarded_iff hp c hc hs s d
  have H2:=ClosedFormulaGateTruth.canonical_point_language_guarded_iff (pointQuery c s d)
    (PositiveMarginSource.source_closed F c) (PositiveMarginSource.description_wellFormed F c (source_scope c))
  constructor
  · intro H
    obtain ⟨HV,HP⟩ := H1.mp H
    exact ⟨HV,(H2.mp HP).2⟩
  · rintro ⟨HV,HP⟩
    exact H1.mpr ⟨HV,H2.mpr ⟨prepared_valid_of_valid c p s d HV,HP⟩⟩

theorem dimension_point (q : PointQuery) : ClosedFormulaGateMetadata.dimension (Input.point q).encode=q.space.dimension := by
  unfold ClosedFormulaGateMetadata.dimension
  rw [Input.field_point_dimension,Codec.unaryValue_toBits]

theorem canonical_point_language_guarded_iff (q : PointQuery)
    (hp : OpenFormulaMargin.Open q.space.formula) (hq : q.space.WellFormed) :
    (Input.point q).encode∈pointLanguage ↔
      (Input.point q).encode∈EndpointValidation.validEndpointLanguage ∧ pointWriter (Input.point q).encode∈pointLanguage := by
  have HC : FormulaView.normalize (Input.field 2 (Input.point q).encode)=q.space.formula.encode := by
    rw [Input.field_point_space,FormulaView.normalize_encode]
  have HS : q.space.formula.arity≤ClosedFormulaGateMetadata.dimension (Input.point q).encode := by rw [dimension_point]; exact hq
  have H:=point_language_equation_guarded_iff hp (Input.point q).encode HC HS q.source q.target
  have HE : PointQuery.mk (Description.mk (ClosedFormulaGateMetadata.dimension (Input.point q).encode) q.space.formula) q.source q.target=q := by rw [dimension_point]
  have H3:=ClosedFormulaGateTruth.endpointField_point 3 q (Or.inl rfl)
  have H4:=ClosedFormulaGateTruth.endpointField_point 4 q (Or.inr rfl)
  simp only [ite_true] at H3
  simp only [show (4 : ℕ)≠3 by decide,ite_false] at H4
  simpa only [HE,pointWriter,preparedPoint,H3,H4] using H

end LeanCanny.Connectivity.OpenFormulaMarginValues
