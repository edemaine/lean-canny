/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotCenteredRadialGraph
public import LeanCanny.Encoding.BoundedFullCriticalSamples
/-! # Native fixed-coordinate radial source and its actual regularized producer -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotCenteredRadialSource
open ETR LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  ClosedFormulaGateMetadata.atom ClosedFormulaGateMetadata.kind FormulaSignSlotMargin.prepared
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotSource.dimension

noncomputable def row (c : List Bool) := TermCoordinateGraph.row (N c+d c) (CenteredSquaredDistanceTerm.term (N c) (d c))
noncomputable def equation (c : List Bool) : Term := .add (row c).square (.add (p c).square (.const 0))
noncomputable def dimension (c : List Bool) := N c+d c+1

theorem dimension_unary : UnaryFn dimension :=
  (FormulaSignSlotMargin.initialDimension_unary.add FormulaSignSlotSource.dimension_unary).add (UnaryFn.const 1)

theorem row_FP : (fun c => (row c).toData.toBits)∈FP := by
  have HT := CenteredSquaredDistanceTerm.term_FP FormulaSignSlotMargin.initialDimension_unary FormulaSignSlotSource.dimension_unary
  have HV : (fun c => (Term.var (N c+d c)).toData.toBits)∈FP :=
    mem_FP_of_eq (Term.variableBits_mem_FP
      (FormulaSignSlotMargin.initialDimension_unary.add FormulaSignSlotSource.dimension_unary)) (fun _ => Term.variableBits_eq _)
  have HN : (fun c => (Term.mul (.const (-1)) (CenteredSquaredDistanceTerm.term (N c) (d c))).toData.toBits)∈FP :=
    mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) HT)
      (fun _ => (Term.mul_toBits _ _).symm)
  exact mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 HV HN) (fun _ => (Term.add_toBits _ _).symm)

theorem equation_FP : (fun c => (equation c).toData.toBits)∈FP := by
  have HP := FormulaSignSlotMargin.initialPolynomial_FP
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 row_FP row_FP)
    (Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 HP HP) (constFn_mem_FP (Term.const 0).toData.toBits)))
  intro c
  simp only [equation,Term.square,Term.add_toBits,Term.mul_toBits]

theorem scope (c : List Bool) : (equation c).arity≤dimension c := by
  have HP := (FormulaSignSlotCenteredRadialGraph.scope c).trans (Nat.le_add_right (N c) (d c))
  have HR := TermCoordinateGraph.row_scope (N c+d c) (CenteredSquaredDistanceTerm.term (N c) (d c))
    (CenteredSquaredDistanceTerm.scope (N c) (d c))
  change (row c).arity≤dimension c at HR
  simp only [equation,Term.arity,Term.square,max_self,max_zero]
  exact max_le HR (HP.trans (Nat.le_succ _))

theorem zero_iff (c : List Bool) (env : ℕ → ℝ) : (equation c).eval env=0 ↔
    (CenteredRadialGraph.description (N c) (d c) (p c)).formula.Holds env := by
  change (SumSquares.accumulate [p c,row c] (.const 0)).eval env=0 ↔ _
  rw [SumSquares.accumulate_zero_iff]
  simp only [List.forall_mem_cons]
  simp
  rfl

noncomputable def readers : BoundedFullWriter.Readers where
  source q := (equation (pairFst q)).toData.toBits
  dim q := dimension (pairFst q)
  radius q := Nat.fromBitsLE (pairSnd q)

theorem access : readers.PolyTime where
  source := mem_FP_comp (f:=pairFst) (g:=fun c => (equation c).toData.toBits) pairFst_mem_FP equation_FP
  dim := dimension_unary.comp pairFst_mem_FP
  radius := BinaryFn.fromBits pairSnd_mem_FP

theorem source_scope (q : List Bool) : (TermView.term (readers.source q)).arity≤readers.dim q := by
  change (TermView.term (equation (pairFst q)).toData.toBits).arity≤_
  rw [TermView.term_toBits]
  exact scope (pairFst q)

theorem degree_same_root (q r : List Bool) (H : pairFst q=pairFst r) :
    BoundedFullWriter.degree readers q=BoundedFullWriter.degree readers r := by
  change BoundedZeroSource.powerDegree (TermView.term (equation (pairFst q)).toData.toBits).toData.size=
    BoundedZeroSource.powerDegree (TermView.term (equation (pairFst r)).toData.toBits).toData.size
  rw [H]

theorem source_regular (q : List Bool) (x : Fin (readers.dim q+4) → ℝ)
    (hx : (BoundedFullCriticalSamples.realPolynomial readers q).eval x=0) :
    Function.Surjective (fderiv ℝ (fun y => (BoundedFullCriticalSamples.realPolynomial readers q).eval y) x) :=
  BoundedFullCriticalSamples.source_regular readers q x hx

theorem exists_joined_sample (q : List Bool) (x : Fin (readers.dim q+4) → ℝ)
    (hx : (BoundedFullCriticalSamples.realPolynomial readers q).eval x=0) :
    ∃ y : BoundedFullCriticalSamples.Samples readers q,
      JoinedIn {z | (BoundedFullCriticalSamples.realPolynomial readers q).eval z=0} x y.val :=
  BoundedFullCriticalSamples.exists_joined_sample readers q x hx

end LeanCanny.Encoding.FormulaSignSlotCenteredRadialSource
