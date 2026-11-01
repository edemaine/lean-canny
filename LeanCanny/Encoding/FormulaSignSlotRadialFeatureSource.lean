/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialFeature
/-! # Native initial writers for the retained quadratic radial feature

Every size/degree bound is computed once from the original input. Recursive
frames retain this source, while centers and radii occur only in affine rows.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialFeatureSource
open ETR LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry
open FormulaSignSlotRadialFeature
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  ClosedFormulaGateMetadata.atom ClosedFormulaGateMetadata.kind FormulaSignSlotMargin.prepared
  FormulaSignSlotMargin.initialDimension FormulaSignSlotMargin.initialPolynomial FormulaSignSlotSource.dimension

noncomputable def row (c : List Bool) := TermCoordinateGraph.row (FormulaSignSlotMargin.initialDimension c)
  (SquaredNormTerm.term (FormulaSignSlotSource.dimension c))

theorem row_FP : (fun c => (row c).toData.toBits)∈FP := by
  have HV : (fun c => (Term.var (FormulaSignSlotMargin.initialDimension c)).toData.toBits)∈FP :=
    mem_FP_of_eq (Term.variableBits_mem_FP FormulaSignSlotMargin.initialDimension_unary)
      (fun _ => Term.variableBits_eq _)
  have HT := SquaredNormTerm.term_FP FormulaSignSlotSource.dimension_unary
  have HN : (fun c => (Term.mul (.const (-1)) (SquaredNormTerm.term (FormulaSignSlotSource.dimension c))).toData.toBits)∈FP :=
    mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) HT)
      (fun _ => (Term.mul_toBits _ _).symm)
  exact mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 HV HN) (fun _ => (Term.add_toBits _ _).symm)

theorem formula_FP : (fun c => (description c).formula.encode)∈FP := by
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 4
    (Codec.taggedOne_mem_FP 1 FormulaSignSlotMargin.initialPolynomial_FP) (Codec.taggedOne_mem_FP 1 row_FP))
  intro c
  simp only [description,TermCoordinateGraph.description,TermCoordinateGraph.formula,row,
    Formula.encode,Formula.toData,Codec.taggedTwo_toBits,Codec.taggedOne_toBits]

theorem closed (c : List Bool) : ClosedFormulaWitness.Closed (description c).formula :=
  .and (.eqZero _) (.eqZero _)

theorem wellFormed (c : List Bool) : (description c).WellFormed :=
  TermCoordinateGraph.description_wellFormed _ _ _ (source_scope c)
    ((SquaredNormTerm.scope _).trans (old_dimension_le c))

noncomputable def prepared (c : List Bool) := (Input.whole (description c)).encode
attribute [local irreducible] prepared

theorem prepared_FP : prepared∈FP := by
  unfold prepared
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 1
    (Codec.unary_toBits_mem_FP (FormulaSignSlotMargin.initialDimension_unary.add (UnaryFn.const 1))) formula_FP)
  intro c
  simp only [Codec.taggedTwo_toBits,Input.encode,Input.toData,Formula.encode,description,TermCoordinateGraph.description]

noncomputable def writer (c : List Bool) := ClosedFormulaBoundedGate.writer (prepared c)

theorem writer_FP : writer∈FP := by
  unfold writer
  exact mem_FP_comp (f:=prepared) (g:=ClosedFormulaBoundedGate.writer) prepared_FP ClosedFormulaBoundedGate.writer_FP

theorem writer_language (c : List Bool) : writer c∈connectedLanguage ↔
    (Input.whole (description c)).encode∈connectedLanguage := by
  unfold writer prepared
  exact ClosedFormulaBoundedGate.canonical_language_iff _ (closed c) (wellFormed c)

noncomputable def initialDegree (c : List Bool) :=
  BoundedMonotoneGateSource.degreeBudget ClosedFormulaGateTruth.F (prepared c)
noncomputable def initialPolynomial (c : List Bool) :=
  BoundedMonotoneGateSource.polynomial ClosedFormulaGateTruth.F (prepared c)

theorem initialDegree_unary : UnaryFn initialDegree := by
  unfold initialDegree
  exact UnaryFn.comp (f:=BoundedMonotoneGateSource.degreeBudget ClosedFormulaGateTruth.F) (g:=prepared)
    (BoundedMonotoneGateSource.degreeBudget_unary _ ClosedFormulaGateMetadata.access) prepared_FP

theorem initialPolynomial_FP : (fun c => (initialPolynomial c).toData.toBits)∈FP := by
  unfold initialPolynomial
  exact mem_FP_comp (f:=prepared)
    (g:=fun q => (BoundedMonotoneGateSource.polynomial ClosedFormulaGateTruth.F q).toData.toBits)
    prepared_FP (BoundedMonotoneGateSource.polynomial_FP _ ClosedFormulaGateMetadata.access)

theorem initialPolynomial_degree (c : List Bool) : (initialPolynomial c).toPolynomial.totalDegree ≤ initialDegree c :=
  BoundedMonotoneGateSource.polynomial_totalDegree_budget ClosedFormulaGateTruth.F (prepared c)

end LeanCanny.Encoding.FormulaSignSlotRadialFeatureSource
