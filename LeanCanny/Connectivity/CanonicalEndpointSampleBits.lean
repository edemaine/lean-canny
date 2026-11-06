/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliarySampleEndpoints
public import LeanCanny.Encoding.FormulaSignSlotSubformulaTest
/-! # Native writers expose the endpoint formulas to the original sign cover -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalEndpointSampleBits
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def formula (k : ℕ) (c : List Bool) := FormulaView.normalize (Input.field k c)
theorem formula_FP (k : ℕ) : formula k ∈ FP := mem_FP_comp (Input.field_mem_FP k) FormulaView.normalize_mem_FP

def tautology (k : ℕ) (c : List Bool) := Codec.taggedTwo 5 (formula k c) (Codec.taggedOne 3 (formula k c))
theorem tautology_FP (k : ℕ) : tautology k ∈ FP := Codec.taggedTwo_mem_FP 5 (formula_FP k)
  (Codec.taggedOne_mem_FP 3 (formula_FP k))

def exposedFormula (c : List Bool) := Codec.taggedTwo 4 (formula 2 c)
  (Codec.taggedTwo 4 (tautology 3 c) (tautology 4 c))
theorem exposedFormula_FP : exposedFormula ∈ FP := Codec.taggedTwo_mem_FP 4 (formula_FP 2)
  (Codec.taggedTwo_mem_FP 4 (tautology_FP 3) (tautology_FP 4))

def frame (c : List Bool) := wrap ((Codec.unary 1).toBits ++ Input.field 1 c ++ exposedFormula c)
theorem frame_FP : frame ∈ FP := mem_FP_comp (appendFn_mem_FP
  (appendFn_mem_FP (constFn_mem_FP _) (Input.field_mem_FP 1)) exposedFormula_FP) wrap_mem_FP

def headBits (side : Bool) (c : List Bool) :=
  FormulaBooleanCircuitSource.header 4 ++ formula 2 c ++ FormulaBooleanCircuitSource.header 4 ++
    (if side then tautology 3 c else []) ++ FormulaBooleanCircuitSource.header 5

theorem headBits_FP (side : Bool) : headBits side ∈ FP := by
  cases side
  · exact appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
      (appendFn_mem_FP (constFn_mem_FP _) (formula_FP 2)) (constFn_mem_FP _)) (constFn_mem_FP _)) (constFn_mem_FP _)
  · exact appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
      (appendFn_mem_FP (constFn_mem_FP _) (formula_FP 2)) (constFn_mem_FP _)) (tautology_FP 3)) (constFn_mem_FP _)

theorem formula_point (q : PointQuery) : exposedFormula (Input.point q).encode =
    (CanonicalAuxiliarySampleEndpoints.expose q).space.formula.encode := by
  simp only [exposedFormula,tautology,formula,Input.field_point_space,Input.field_point_source,
    Input.field_point_target,FormulaView.normalize_encode]
  simp only [CanonicalAuxiliarySampleEndpoints.expose,Formula.encode,Formula.toData,
    Codec.taggedOne_toBits,Codec.taggedTwo_toBits]

theorem frame_point (q : PointQuery) : frame (Input.point q).encode =
    CanonicalSignRefinement.original (CanonicalAuxiliarySampleEndpoints.expose q).space := by
  rw [frame,formula_point,Input.field_point_dimension]
  simp [CanonicalSignRefinement.original,CanonicalAuxiliarySampleEndpoints.expose,Input.encode,
    Input.toData,Formula.encode,Data.toBits_l,wrap,List.append_assoc]

theorem prefix_source_point (q : PointQuery) : headBits false (Input.point q).encode =
    CanonicalAuxiliarySampleEndpoints.sourcePrefix q := by
  simp only [headBits,formula,Input.field_point_space,FormulaView.normalize_encode,Bool.false_eq_true,ite_false,
    List.append_nil]
  rfl

theorem prefix_target_point (q : PointQuery) : headBits true (Input.point q).encode =
    CanonicalAuxiliarySampleEndpoints.targetPrefix q := by
  simp only [headBits,formula,tautology,Input.field_point_space,Input.field_point_source,FormulaView.normalize_encode,ite_true]
  simp only [CanonicalAuxiliarySampleEndpoints.targetPrefix,Formula.encode,Formula.toData,
    Codec.taggedOne_toBits,Codec.taggedTwo_toBits]


noncomputable def query (side : Bool) (z : List Bool) := pair
  (CanonicalAuxiliaryCandidateLabels.source (pair (frame (pairFst z)) (pairSnd z)))
  (headBits side (pairFst z))
theorem query_FP (side : Bool) : query side ∈ FP := by
  have HP : (fun z => pair (frame (pairFst z)) (pairSnd z)) ∈ FP :=
    mem_FP_pair (mem_FP_comp (f:=pairFst) (g:=frame) pairFst_mem_FP frame_FP) pairSnd_mem_FP
  have HS : (fun z => CanonicalAuxiliaryCandidateLabels.source (pair (frame (pairFst z)) (pairSnd z))) ∈ FP :=
    mem_FP_comp (f:=fun z => pair (frame (pairFst z)) (pairSnd z))
      (g:=CanonicalAuxiliaryCandidateLabels.source) HP CanonicalAuxiliaryCandidateLabels.source_FP
  have HH : (fun z => headBits side (pairFst z)) ∈ FP :=
    mem_FP_comp (f:=pairFst) (g:=headBits side) pairFst_mem_FP (headBits_FP side)
  exact mem_FP_pair HS HH

noncomputable def value (side : Bool) (z : List Bool) := FormulaSignSlotSubformulaTest.value (query side z)
theorem evaluator (side : Bool) : SpaceFunction (fun z => [value side z]) :=
  (FormulaSignSlotSubformulaTest.evaluator.precompose (query side) (query_FP side))

private theorem sample_truth (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d)
    (hi : CanonicalAuxiliaryProjectedSamples.Good d i) (p : Formula) (pre suffix : List Bool)
    (hc : FormulaView.normalize (Input.field 2 (CanonicalSignRefinement.original d)) = pre ++ p.encode ++ suffix)
    (hp : p.arity ≤ d.dimension) :
    FormulaSignSlotSubformulaTest.value (pair (CanonicalSignRefinement.source d i.1) pre) =
      decide (p.Holds (Formula.extend (CanonicalAuxiliaryCandidateCover.rawSample d i hi))) := by
  have HD : ClosedFormulaGateMetadata.dimension (CanonicalSignRefinement.original d) = d.dimension := by
    change ClosedFormulaGateTruth.F.dimension (Input.whole d).encode = d.dimension
    exact ClosedFormulaGateTruth.dimension_whole d
  exact FormulaSignSlotSubformulaTest.packet (CanonicalSignRefinement.original d) i.1.val _
    (CanonicalAuxiliaryPieceTruth.raw_stratum d i _ (CanonicalAuxiliaryCandidateCover.rawSample_mem d i hi))
    p pre suffix hc (HD.symm ▸ hp)

/-- The native source-endpoint bit is the literal formula truth at this same
accepted auxiliary sample. Singleton validation is performed separately. -/
theorem value_source_point (q : PointQuery)
    (i : CanonicalAuxiliaryCandidateCover.Index (CanonicalAuxiliarySampleEndpoints.expose q).space)
    (hi : CanonicalAuxiliaryProjectedSamples.Good (CanonicalAuxiliarySampleEndpoints.expose q).space i)
    (hp : q.source.arity ≤ q.space.dimension) :
    value false (pair (Input.point q).encode (CanonicalAuxiliaryCandidateCover.encode _ i)) =
      decide (q.source.Holds (Formula.extend (CanonicalAuxiliaryCandidateCover.rawSample _ i hi))) := by
  have HQ : query false (pair (Input.point q).encode (CanonicalAuxiliaryCandidateCover.encode _ i)) =
      pair (CanonicalSignRefinement.source _ i.1) (CanonicalAuxiliarySampleEndpoints.sourcePrefix q) := by
    simp only [query,pairFst_pair,pairSnd_pair,frame_point,CanonicalAuxiliaryCandidateLabels.source_encode,
      prefix_source_point]
  rw [value,HQ]
  exact sample_truth _ i hi q.source _ _ (CanonicalAuxiliarySampleEndpoints.source_occurs q) hp

theorem value_target_point (q : PointQuery)
    (i : CanonicalAuxiliaryCandidateCover.Index (CanonicalAuxiliarySampleEndpoints.expose q).space)
    (hi : CanonicalAuxiliaryProjectedSamples.Good (CanonicalAuxiliarySampleEndpoints.expose q).space i)
    (hp : q.target.arity ≤ q.space.dimension) :
    value true (pair (Input.point q).encode (CanonicalAuxiliaryCandidateCover.encode _ i)) =
      decide (q.target.Holds (Formula.extend (CanonicalAuxiliaryCandidateCover.rawSample _ i hi))) := by
  have HQ : query true (pair (Input.point q).encode (CanonicalAuxiliaryCandidateCover.encode _ i)) =
      pair (CanonicalSignRefinement.source _ i.1) (CanonicalAuxiliarySampleEndpoints.targetPrefix q) := by
    simp only [query,pairFst_pair,pairSnd_pair,frame_point,CanonicalAuxiliaryCandidateLabels.source_encode,
      prefix_target_point]
  rw [value,HQ]
  exact sample_truth _ i hi q.target _ _ (CanonicalAuxiliarySampleEndpoints.target_occurs q) hp

end LeanCanny.Connectivity.CanonicalEndpointSampleBits
