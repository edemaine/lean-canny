/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ImplicitSourceGramSliceNative
public import LeanCanny.Algebra.UnivariateRowSpace
/-! # Closed native access to the implicit witnessed coercive Gram grid -/
@[expose] public section
namespace LeanCanny.Encoding.ImplicitSourceGramGrid
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem count_unary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) : UnaryFn (count S) :=
  A.arity.comp pairFst_mem_FP

theorem degree_binary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) : BinaryFn (degree S) :=
  (ImplicitSourceCoerciveBoxGram.degreeBound_binary S A).comp pairFst_mem_FP

theorem mass_binary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) : BinaryFn (mass S) :=
  (ImplicitSourceCoerciveBoxGram.massExponent_binary S A).comp pairFst_mem_FP

theorem annHeight_binary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) :
    BinaryFn (fun c => mass S c+1) := (mass_binary S A).add (BinaryFn.const 1)

noncomputable def selected (S : Source) (hp : ∀ u, 0<S.arity u) (q : List Bool) :
    Fin (count S (SquareSampleInput.source q)) :=
  SquareSampleInput.selected (input S hp) (SquareSampleInput.source q) (SquareSampleInput.indexWord q)

theorem selected_unary (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0<S.arity u) : UnaryFn (fun q => (selected S hp q).val) :=
  UnaryFn.fromBitsLE_min SquareSampleInput.indexWord_FP
    (((count_unary S A).comp SquareSampleInput.source_FP).sub (UnaryFn.const 1))

private theorem selected_polynomial_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0<S.arity u) : SpaceFunction (PrimitivePairBits.coefficient
      (fun q => polynomial S (SquareSampleInput.source q) (selected S hp q))) := by
  let C := RationalSubstitution.IntegerBits.context
  have ER : (SquareSampleInput.source ∘ C) ∈ FP :=
    mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP SquareSampleInput.source_FP
  have HI : BinaryFn (fun q => (selected S hp (C q)).val) :=
    (BinaryFn.ofUnary (selected_unary S A hp)).comp RationalSubstitution.IntegerBits.context_mem_FP
  have E := ImplicitSourceGramSliceNative.evaluator S A (SquareSampleInput.source ∘ C)
    (fun q => (selected S hp (C q)).val)
    (fun q => Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree q)) pairSnd
    ER HI (BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP
  refine E.congr (funext fun q => ?_)
  unfold ImplicitSourceGramSliceNative.value PrimitivePairBits.coefficient
  rw [ImplicitSourceGramSliceNative.polynomial_eq]
  rfl

theorem row_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0<S.arity u) : SpaceFunction (SquareSampleInput.rowCoefficient (input S hp)) := by
  have E := UnivariateRowBits.evaluator ((count_unary S A).comp SquareSampleInput.source_FP)
    (UnaryFn.length SquareSampleInput.widthWord_FP) (selected S hp) (selected_unary S A hp)
    (fun q => polynomial S (SquareSampleInput.source q) (selected S hp q))
    (selected_polynomial_evaluator S A hp) SquareSampleInput.rankWord_FP SquareSampleInput.modulusWord_FP
  exact E.congr (funext fun _ => rfl)

theorem ann_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0<S.arity u) : SpaceFunction (SquareSampleInput.annCoefficient (input S hp)) := by
  have E := ImplicitSourceGramSliceNative.evaluator S A SquareSampleInput.source
    (fun q => (selected S hp q).val) (fun q => Nat.fromBitsLE (SquareSampleInput.rankWord q))
    SquareSampleInput.modulusWord SquareSampleInput.source_FP
    (BinaryFn.ofUnary (selected_unary S A hp)) (BinaryFn.fromBits SquareSampleInput.rankWord_FP)
    SquareSampleInput.modulusWord_FP
  refine E.congr (funext fun q => ?_)
  unfold ImplicitSourceGramSliceNative.value SquareSampleInput.annCoefficient SquareSampleInput.annValue
  rw [ImplicitSourceGramSliceNative.polynomial_eq]
  simp only [input,selected]

theorem access (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0<S.arity u) : (input S hp).Access :=
  ⟨count_unary S A,(degree_binary S A).add (BinaryFn.const 1),mass_binary S A,
    degree_binary S A,annHeight_binary S A,row_evaluator S A hp,ann_evaluator S A hp⟩

end LeanCanny.Encoding.ImplicitSourceGramGrid
