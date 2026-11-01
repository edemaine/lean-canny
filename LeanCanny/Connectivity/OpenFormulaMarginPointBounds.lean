/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.OpenFormulaMarginPointWriter
public import LeanCanny.Encoding.MonotoneGateNativeBounds
/-! # One native original-input dimension and degree cap for the actual point-output equation -/
@[expose] public section
namespace LeanCanny.Connectivity.OpenFormulaMarginValues
open ETR LeanCanny.Encoding LeanCanny.Computation
attribute [local irreducible] preparedPoint

noncomputable def pointPolynomial (c : List Bool) : Term :=
  MonotoneGateSource.polynomial ClosedFormulaGateMetadata.family (preparedPoint c)
noncomputable def pointSpace (c : List Bool) : Description :=
  MonotoneGateGraph.description ClosedFormulaGateMetadata.family (preparedPoint c)
noncomputable def pointDimensionBudget (c : List Bool) : ℕ := (pointSpace c).dimension
noncomputable def pointDegreeBudget (c : List Bool) : ℕ :=
  MonotoneGateSource.degreeBudget ClosedFormulaGateMetadata.family (preparedPoint c)

theorem pointPolynomial_FP : (fun c => (pointPolynomial c).toData.toBits) ∈ FP :=
  mem_FP_comp (f := preparedPoint)
    (g := fun w => (MonotoneGateSource.polynomial ClosedFormulaGateMetadata.family w).toData.toBits)
    preparedPoint_FP ClosedFormulaGateMetadata.source_FP

theorem pointDimensionBudget_unary : UnaryFn pointDimensionBudget :=
  (MonotoneGateGraph.description_dim_unary ClosedFormulaGateMetadata.family ClosedFormulaGateMetadata.access).comp preparedPoint_FP

theorem pointDegreeBudget_unary : UnaryFn pointDegreeBudget :=
  (MonotoneGateSource.degreeBudget_unary ClosedFormulaGateMetadata.family ClosedFormulaGateMetadata.access).comp preparedPoint_FP

theorem pointPolynomial_degree (c : List Bool) : (pointPolynomial c).toPolynomial.totalDegree≤pointDegreeBudget c :=
  MonotoneGateSource.polynomial_totalDegree_budget _ _

theorem pointSpace_formula (c : List Bool) : (pointSpace c).formula=.eqZero (pointPolynomial c) := rfl

theorem pointSpace_wellFormed (c : List Bool) : (pointSpace c).WellFormed :=
  MonotoneGateGraph.description_wellFormed _ _ (fun i _ => by
    simpa only [ClosedFormulaGateMetadata.family,pairFst_pair] using
      ClosedFormulaGateMetadata.atom_scope (pair (preparedPoint c) (List.replicate i true)))

end LeanCanny.Connectivity.OpenFormulaMarginValues
