/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ClosedFormulaGatePoints
/-! # Native canonical point-query records for the closed Boolean gate reduction -/
@[expose] public section
namespace LeanCanny.Encoding.ClosedFormulaGatePointWriter
open LeanCanny.Computation ETR LeanCanny.Connectivity
open scoped Classical

theorem point_record_FP {s d : List Bool → Formula}
    (hs : (fun c => (s c).encode) ∈ FP) (hd : (fun c => (d c).encode) ∈ FP) :
    (fun c => (Input.point (ClosedFormulaGateTruth.pointQuery c (s c) (d c))).encode) ∈ FP := by
  have HN := MonotoneGateGraph.description_dim_unary ClosedFormulaGateTruth.F ClosedFormulaGateMetadata.access
  have HS := MonotoneGateEndpoint.endpoint_FP ClosedFormulaGateTruth.F ClosedFormulaGateMetadata.access hs
  have HD := MonotoneGateEndpoint.endpoint_FP ClosedFormulaGateTruth.F ClosedFormulaGateMetadata.access hd
  have HG : (fun c => (Formula.eqZero (MonotoneGateSource.polynomial ClosedFormulaGateTruth.F c)).encode) ∈ FP := by
    apply mem_FP_of_eq (Codec.taggedOne_mem_FP 1 ClosedFormulaGateMetadata.source_FP)
    intro c
    exact Codec.taggedOne_toBits 1 _
  have H := mem_FP_comp (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
    (appendFn_mem_FP (constFn_mem_FP (Codec.unary 0).toBits) (Codec.unary_toBits_mem_FP HN)) HG) HS) HD) Brackets.wrap_mem_FP
  apply mem_FP_of_eq H
  intro c
  simp only [Function.comp_apply,Input.encode,Input.toData,Data.toBits_l,Brackets.wrap,List.map_cons,List.map_nil,
    List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc,ClosedFormulaGateTruth.pointQuery,
    MonotoneGateGraph.description,Formula.encode]

noncomputable def endpointField (k : ℕ) (c : List Bool) : Formula := FormulaView.formula (Input.field k c)

theorem endpointField_FP (k : ℕ) : (fun c => (endpointField k c).encode) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Input.field_mem_FP k) FormulaView.normalize_mem_FP)
    (fun c => FormulaView.normalize_eq_formula (Input.field k c))

noncomputable def writer (c : List Bool) : List Bool :=
  (Input.point (ClosedFormulaGateTruth.pointQuery c (endpointField 3 c) (endpointField 4 c))).encode

theorem writer_FP : writer ∈ FP := point_record_FP (endpointField_FP 3) (endpointField_FP 4)

end LeanCanny.Encoding.ClosedFormulaGatePointWriter
