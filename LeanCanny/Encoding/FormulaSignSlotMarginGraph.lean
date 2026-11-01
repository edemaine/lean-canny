/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotMargin
public import LeanCanny.Geometry.TermCoordinateGraph
public import LeanCanny.Connectivity.ClosedFormulaBoundedGate
public import LeanCanny.Encoding.BoundedMonotoneGateNativeBounds
/-! # A native coordinate objective for the selected strict margin

The polynomial margin is installed as one initial graph coordinate. The
subsequent bounded equation writer has one native initial degree/mass cap;
no recursive frame changes that source cap or assumes polynomial objectives.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotMargin
open ETR LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry FormulaSignSlotSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  FormulaSignSlotSource.dimension FormulaSignSlotSource.count FormulaSignSlotSource.term

noncomputable def graphRow (c : List Bool) := TermCoordinateGraph.row (dimension c) (margin c)
noncomputable def graphDescription (c : List Bool) :=
  TermCoordinateGraph.description (dimension c) (envelope c) (margin c)
def objective (c : List Bool) := dimension c

theorem objective_unary : UnaryFn objective := dimension_unary

theorem graphRow_FP : (fun c => (graphRow c).toData.toBits) ∈ FP := by
  have HV : (fun c => (Term.var (dimension c)).toData.toBits) ∈ FP :=
    mem_FP_of_eq (Term.variableBits_mem_FP dimension_unary) (fun _ => Term.variableBits_eq _)
  have HN : (fun c => (Term.mul (.const (-1)) (margin c)).toData.toBits) ∈ FP :=
    mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) margin_FP)
      (fun _ => (Term.mul_toBits _ _).symm)
  exact mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 HV HN) (fun _ => (Term.add_toBits _ _).symm)

theorem graphFormula_FP : (fun c => (graphDescription c).formula.encode) ∈ FP := by
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 4 envelope_FP (Codec.taggedOne_mem_FP 1 graphRow_FP))
  intro c
  simp only [graphDescription,TermCoordinateGraph.description,TermCoordinateGraph.formula,graphRow,
    Formula.encode,Formula.toData,Codec.taggedTwo_toBits,Codec.taggedOne_toBits]

theorem graph_closed (c : List Bool) : ClosedFormulaWitness.Closed (graphDescription c).formula :=
  .and (envelope_closed c) (.eqZero (graphRow c))

theorem graph_wellFormed (c : List Bool) : (graphDescription c).WellFormed :=
  TermCoordinateGraph.description_wellFormed _ _ _ (envelope_scope c) (margin_scope c)

noncomputable def graphHomeomorph (c : List Bool) :
    (graphDescription c).realization ≃ₜ (FormulaSignSlotSource.description c).realization :=
  TermCoordinateGraph.homeomorph _ _ _ (envelope_scope c) (margin_scope c)

theorem graph_objective (c : List Bool) (y : (graphDescription c).realization) :
    y.val ⟨objective c,by change dimension c < dimension c+1; omega⟩=
      (margin c).eval (Formula.extend (graphHomeomorph c y).val) :=
  TermCoordinateGraph.objective_coordinate _ _ _ (envelope_scope c) (margin_scope c) y

theorem graph_positive (c : List Bool) (y : (graphDescription c).realization) :
    0 < y.val ⟨objective c,by change dimension c < dimension c+1; omega⟩ ↔
      (stratum c).Holds (Formula.extend (graphHomeomorph c y).val) := by
  rw [graph_objective]
  exact margin_positive_iff _ _ (graphHomeomorph c y).property

noncomputable def prepared (c : List Bool) := (Input.whole (graphDescription c)).encode
attribute [local irreducible] prepared

theorem prepared_FP : prepared ∈ FP := by
  unfold prepared
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 1
    (Codec.unary_toBits_mem_FP (dimension_unary.add (UnaryFn.const 1))) graphFormula_FP)
  intro c
  simp only [Codec.taggedTwo_toBits,Input.encode,Input.toData,Formula.encode,graphDescription,
    TermCoordinateGraph.description]

noncomputable def writer (c : List Bool) := ClosedFormulaBoundedGate.writer (prepared c)
theorem writer_FP : writer ∈ FP := by
  unfold writer
  exact mem_FP_comp (f := prepared) (g := ClosedFormulaBoundedGate.writer) prepared_FP ClosedFormulaBoundedGate.writer_FP

theorem writer_graph_language (c : List Bool) : writer c∈connectedLanguage ↔
    (Input.whole (graphDescription c)).encode∈connectedLanguage := by
  unfold writer prepared
  exact ClosedFormulaBoundedGate.canonical_language_iff _ (graph_closed c) (graph_wellFormed c)

noncomputable def initialDegree (c : List Bool) :=
  BoundedMonotoneGateSource.degreeBudget ClosedFormulaGateTruth.F (prepared c)
noncomputable def initialDimension (c : List Bool) :=
  BoundedMonotoneGateSource.total ClosedFormulaGateTruth.F (prepared c)
noncomputable def initialPolynomial (c : List Bool) :=
  BoundedMonotoneGateSource.polynomial ClosedFormulaGateTruth.F (prepared c)

theorem initialDegree_unary : UnaryFn initialDegree := by
  unfold initialDegree
  exact UnaryFn.comp (f := BoundedMonotoneGateSource.degreeBudget ClosedFormulaGateTruth.F) (g := prepared)
    (BoundedMonotoneGateSource.degreeBudget_unary _ ClosedFormulaGateMetadata.access) prepared_FP
theorem initialDimension_unary : UnaryFn initialDimension := by
  unfold initialDimension
  exact UnaryFn.comp (f := BoundedMonotoneGateSource.total ClosedFormulaGateTruth.F) (g := prepared)
    (BoundedMonotoneGateSource.total_unary _ ClosedFormulaGateMetadata.access) prepared_FP
theorem initialPolynomial_FP : (fun c => (initialPolynomial c).toData.toBits) ∈ FP := by
  unfold initialPolynomial
  exact mem_FP_comp (f := prepared)
    (g := fun q => (BoundedMonotoneGateSource.polynomial ClosedFormulaGateTruth.F q).toData.toBits)
    prepared_FP (BoundedMonotoneGateSource.polynomial_FP _ ClosedFormulaGateMetadata.access)
theorem initialPolynomial_degree (c : List Bool) : (initialPolynomial c).toPolynomial.totalDegree ≤ initialDegree c := by
  unfold initialPolynomial initialDegree
  exact BoundedMonotoneGateSource.polynomial_totalDegree_budget ClosedFormulaGateTruth.F (prepared c)

end LeanCanny.Encoding.FormulaSignSlotMargin
