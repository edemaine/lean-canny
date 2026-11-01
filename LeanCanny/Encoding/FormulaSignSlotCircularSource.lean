/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotCircularInterior
public import LeanCanny.Encoding.FormulaSignSlotRadialEquation
/-! # Native closed circular margin source and its original degree budget

Two literal equations are squared once. The circle witnesses are appended
before any recursive frames; their source and degree are fixed throughout
all later slices. These are actual formula/term writers, not evaluator input.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotCircularSource
open ETR LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry
open FormulaSignSlotCircularInterior
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotSource.dimension

noncomputable def dimension (c : List Bool) := FormulaSignSlotMargin.initialDimension c+2
noncomputable def row (c : List Bool) := FormulaStrictWitness.term (FormulaSignSlotMargin.initialDimension c) (negativeMargin c)
noncomputable def equation (c : List Bool) : Term := .add (row c).square
  (.add (FormulaSignSlotMargin.initialPolynomial c).square (.const 0))

theorem dimension_unary : UnaryFn dimension := FormulaSignSlotMargin.initialDimension_unary.add (UnaryFn.const 2)

theorem negativeMargin_FP : (fun c => (negativeMargin c).toData.toBits)∈FP := by
  have H := Term.variableBits_mem_FP FormulaSignSlotMargin.objective_unary
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) H)
  intro c
  simp only [negativeMargin,FormulaSignSlotMarginProjection.objectiveIndex,Term.mul_toBits,Term.variableBits_eq]

theorem row_FP : (fun c => (row c).toData.toBits)∈FP :=
  FormulaStrictWitness.term_bits_FP FormulaSignSlotMargin.initialDimension_unary negativeMargin_FP

theorem equation_FP : (fun c => (equation c).toData.toBits)∈FP := by
  have HP := FormulaSignSlotMargin.initialPolynomial_FP
  have HR := row_FP
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 HR HR)
    (Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 HP HP) (constFn_mem_FP (Term.const 0).toData.toBits)))
  intro c
  simp only [equation,Term.square,Term.add_toBits,Term.mul_toBits]

theorem whole_FP : (fun c => (Input.whole (description c)).encode)∈FP := by
  have HP : (fun c => (Formula.eqZero (FormulaSignSlotMargin.initialPolynomial c)).encode)∈FP :=
    mem_FP_of_eq (Codec.taggedOne_mem_FP 1 FormulaSignSlotMargin.initialPolynomial_FP)
      (fun c => by simp only [Formula.encode,Formula.toData,Codec.taggedOne_toBits])
  exact FormulaStrictWitness.whole_record_FP FormulaSignSlotMargin.initialDimension_unary HP negativeMargin_FP

theorem scope (c : List Bool) : (equation c).arity≤dimension c := by
  have HP := FormulaSignSlotRadialFeature.source_scope c
  have HR := FormulaStrictWitness.term_arity (FormulaSignSlotMargin.initialDimension c) (negativeMargin c) (negativeMargin_scope c)
  change (row c).arity≤dimension c at HR
  simp only [equation,Term.arity,Term.square,max_self,max_zero]
  exact max_le HR (HP.trans (Nat.le_add_right _ 2))

theorem zero_iff (c : List Bool) (env : ℕ → ℝ) : (equation c).eval env=0 ↔ (description c).formula.Holds env := by
  change (SumSquares.accumulate [FormulaSignSlotMargin.initialPolynomial c,row c] (.const 0)).eval env=0 ↔ _
  rw [SumSquares.accumulate_zero_iff]
  simp only [List.forall_mem_cons]
  simp
  rfl

noncomputable def polynomial (c : List Bool) := (equation c).finitePolynomial (dimension c)
theorem polynomial_zero (c : List Bool) (x : Fin (dimension c) → ℝ) :
    (polynomial c).eval₂ (Int.castRingHom ℝ) x=0 ↔ (description c).formula.Holds (Formula.extend x) := by
  rw [polynomial,Term.eval_finitePolynomial,zero_iff]

noncomputable def budget (c : List Bool) := (equation c).toData.size
theorem budget_unary : UnaryFn budget := (UnaryFn.length equation_FP).of_eq (fun c => Data.length_toBits (equation c).toData)
theorem polynomial_degree (c : List Bool) : (polynomial c).totalDegree≤budget c :=
  (Term.totalDegree_finitePolynomial _ _).trans (Term.degreeBound_le_dataSize _)
theorem polynomial_mass (c : List Bool) : LeanCanny.Algebra.MvMass.mass (polynomial c)≤2^budget c := Term.finitePolynomial_mass _ _
end LeanCanny.Encoding.FormulaSignSlotCircularSource
