/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialFeatureSource
/-! # The literal radial-feature graph as one native integer equation

Only the two actual graph equations are squared. There is no new witness
compiler and no recursive update of the original source degree.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEquation
open ETR LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  ClosedFormulaGateMetadata.atom ClosedFormulaGateMetadata.kind FormulaSignSlotMargin.prepared
  FormulaSignSlotMargin.initialDimension FormulaSignSlotMargin.initialPolynomial FormulaSignSlotSource.dimension

noncomputable def dimension (c : List Bool) := FormulaSignSlotMargin.initialDimension c+1
noncomputable def equation (c : List Bool) : Term := .add
  (FormulaSignSlotRadialFeatureSource.row c).square
  (.add (FormulaSignSlotMargin.initialPolynomial c).square (.const 0))

theorem dimension_unary : UnaryFn dimension := FormulaSignSlotMargin.initialDimension_unary.add (UnaryFn.const 1)

theorem equation_FP : (fun c => (equation c).toData.toBits)∈FP := by
  have HP := FormulaSignSlotMargin.initialPolynomial_FP
  have HR := FormulaSignSlotRadialFeatureSource.row_FP
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 HR HR)
    (Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 HP HP) (constFn_mem_FP (Term.const 0).toData.toBits)))
  intro c
  simp only [equation,Term.square,Term.add_toBits,Term.mul_toBits]

theorem scope (c : List Bool) : (equation c).arity≤dimension c := by
  have HP := FormulaSignSlotRadialFeature.source_scope c
  have HR := TermCoordinateGraph.row_scope (FormulaSignSlotMargin.initialDimension c)
    (SquaredNormTerm.term (FormulaSignSlotSource.dimension c))
    ((SquaredNormTerm.scope _).trans (FormulaSignSlotRadialFeature.old_dimension_le c))
  change (FormulaSignSlotRadialFeatureSource.row c).arity≤dimension c at HR
  simp only [equation,Term.arity,Term.square,max_self,max_zero]
  exact max_le HR (HP.trans (Nat.le_succ _))

theorem zero_iff (c : List Bool) (env : ℕ → ℝ) : (equation c).eval env=0 ↔
    (FormulaSignSlotRadialFeature.description c).formula.Holds env := by
  change (SumSquares.accumulate [FormulaSignSlotMargin.initialPolynomial c,
    FormulaSignSlotRadialFeatureSource.row c] (.const 0)).eval env=0 ↔ _
  rw [SumSquares.accumulate_zero_iff]
  simp only [List.forall_mem_cons]
  simp
  rfl

noncomputable def polynomial (c : List Bool) := (equation c).finitePolynomial (dimension c)

theorem polynomial_zero (c : List Bool) (x : Fin (dimension c) → ℝ) :
    (polynomial c).eval₂ (Int.castRingHom ℝ) x=0 ↔
      (FormulaSignSlotRadialFeature.description c).formula.Holds (Formula.extend x) := by
  rw [polynomial,Term.eval_finitePolynomial,zero_iff]

noncomputable def budget (c : List Bool) := (equation c).toData.size

theorem budget_unary : UnaryFn budget :=
  (UnaryFn.length equation_FP).of_eq (fun c => Data.length_toBits (equation c).toData)

theorem polynomial_degree (c : List Bool) : (polynomial c).totalDegree≤budget c :=
  (Term.totalDegree_finitePolynomial _ _).trans (Term.degreeBound_le_dataSize _)

theorem polynomial_mass (c : List Bool) : LeanCanny.Algebra.MvMass.mass (polynomial c)≤2^budget c :=
  Term.finitePolynomial_mass _ _

end LeanCanny.Encoding.FormulaSignSlotRadialEquation
