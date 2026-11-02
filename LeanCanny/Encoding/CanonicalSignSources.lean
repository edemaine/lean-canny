/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalSignRefinement
/-! # Native actual source writers for the canonical accepted-sign graph

Point and whole-space records use the same immutable spatial source. The
original dimension/formula fields are retained literally, then a native sign
word selects the constructed closed circular source. Original endpoint fields
do not enter this source. Native polynomial, arity and fixed initial degree
readers are inherited from the actual bounded closed-formula compiler.
-/
@[expose] public section
namespace LeanCanny.Encoding.CanonicalSignSources
open ETR LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def whole (c : List Bool) := Codec.taggedTwo 1 (Input.field 1 c) (Input.field 2 c)
theorem whole_FP : whole∈FP := Codec.taggedTwo_mem_FP 1 (Input.field_mem_FP 1) (Input.field_mem_FP 2)
theorem whole_whole (d : Description) : whole (Input.whole d).encode=(Input.whole d).encode := by
  simp only [whole,Input.field_whole_dimension,Input.field_whole_space]
  exact Codec.taggedTwo_toBits 1 _ _
theorem whole_point (q : PointQuery) : whole (Input.point q).encode=(Input.whole q.space).encode := by
  simp only [whole,Input.field_point_dimension,Input.field_point_space]
  exact Codec.taggedTwo_toBits 1 _ _

noncomputable def source (q : List Bool) := FormulaSignSlotCircularBoundedCover.root (pair (whole (pairFst q)) (pairSnd q))
theorem source_FP : source∈FP :=
  mem_FP_comp (f := fun q => pair (whole (pairFst q)) (pairSnd q)) (g := FormulaSignSlotCircularBoundedCover.root)
    (mem_FP_pair (mem_FP_comp (f := pairFst) (g := whole) pairFst_mem_FP whole_FP) pairSnd_mem_FP) FormulaSignSlotCircularBoundedCover.root_FP

theorem source_whole (d : Description) (l : CanonicalSignRefinement.Label d) :
    source (pair (Input.whole d).encode l.val)=
      FormulaSignSlotCircularBoundedCover.root (CanonicalSignRefinement.source d l) := by
  simp only [source,pairFst_pair,pairSnd_pair,whole_whole,CanonicalSignRefinement.source,CanonicalSignRefinement.original]
theorem source_point (q : PointQuery) (l : CanonicalSignRefinement.Label q.space) :
    source (pair (Input.point q).encode l.val)=
      FormulaSignSlotCircularBoundedCover.root (CanonicalSignRefinement.source q.space l) := by
  simp only [source,pairFst_pair,pairSnd_pair,whole_point,CanonicalSignRefinement.source,CanonicalSignRefinement.original]

noncomputable def labelWidth (c : List Bool) := 2*ClosedFormulaGateMetadata.count (whole c)
theorem labelWidth_unary : UnaryFn labelWidth :=
  (UnaryFn.const 2).mul (ClosedFormulaGateMetadata.count_unary.comp whole_FP)
theorem labelWidth_whole (d : Description) : labelWidth (Input.whole d).encode=CanonicalSignRefinement.width d := by
  rw [labelWidth,whole_whole]
  rfl
theorem labelWidth_point (q : PointQuery) : labelWidth (Input.point q).encode=CanonicalSignRefinement.width q.space := by
  rw [labelWidth,whole_point]
  rfl

attribute [local irreducible] source whole Input.field pair FormulaSignSlotCircularBoundedCover.root

noncomputable def arity (q : List Bool) := BoundedMonotoneGateSource.total ClosedFormulaGateTruth.F (source q)
noncomputable def degree (q : List Bool) := BoundedMonotoneGateSource.degreeBudget ClosedFormulaGateTruth.F (source q)
noncomputable def polynomial (q : List Bool) := BoundedMonotoneGateSource.polynomial ClosedFormulaGateTruth.F (source q)

theorem arity_unary : UnaryFn arity :=
  UnaryFn.comp (f := BoundedMonotoneGateSource.total ClosedFormulaGateTruth.F) (g := source) (BoundedMonotoneGateSource.total_unary _ ClosedFormulaGateMetadata.access) source_FP
theorem degree_unary : UnaryFn degree :=
  UnaryFn.comp (f := BoundedMonotoneGateSource.degreeBudget ClosedFormulaGateTruth.F) (g := source) (BoundedMonotoneGateSource.degreeBudget_unary _ ClosedFormulaGateMetadata.access) source_FP
theorem polynomial_FP : (fun q => (polynomial q).toData.toBits)∈FP :=
  mem_FP_comp (f := source) (g := fun c => (BoundedMonotoneGateSource.polynomial ClosedFormulaGateTruth.F c).toData.toBits) source_FP (BoundedMonotoneGateSource.polynomial_FP _ ClosedFormulaGateMetadata.access)

theorem polynomial_degree (q : List Bool) : (polynomial q).toPolynomial.totalDegree≤degree q :=
  BoundedMonotoneGateSource.polynomial_totalDegree_budget _ (source q)
end LeanCanny.Encoding.CanonicalSignSources
