/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleSource
public import LeanCanny.Algebra.ScaledSquarefreeSpace
public import LeanCanny.Algebra.PreparedPolynomialContext

/-! # Square-free coordinate coefficients from the original native reader

Exact degrees are prepared in space before square-free preprocessing. The
original degree and height allowances remain the only numerical inputs.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleSquarefree
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

noncomputable def preparedPolynomial (F : Inputs) (q : List Bool) : Polynomial ℤ :=
  ScaledSquarefree.polynomial ((SquareSampleSource.family F).polynomial q)

noncomputable def polynomial (F : Inputs) (q : List Bool) : Polynomial ℤ :=
  ScaledSquarefree.polynomial (SquareSampleSource.polynomial F q)

lemma polynomial_pair (F : Inputs) (u i : List Bool) : polynomial F (pair u i) =
    ScaledSquarefree.polynomial (F.annihilator u (SquareSampleInput.selected F u i)) := by
  let read (u i : List Bool) := ScaledSquarefree.polynomial (F.annihilator u (SquareSampleInput.selected F u i))
  change read (pairFst (pair u i)) (pairSnd (pair u i)) = read u i
  rw [pairFst_pair, pairSnd_pair]

def query (q : List Bool) := pair (pair (RationalSubstitution.IntegerBits.context q) (pairSnd q))
  (RationalSubstitution.IntegerBits.selectedDegree q)

theorem query_FP : query ∈ FP := mem_FP_pair
  (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
  RationalSubstitution.IntegerBits.selectedDegree_mem_FP

theorem prepared_evaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (PrimitivePairBits.coefficient (preparedPolynomial F)) := by
  have E := SeparableBits.squarefreeEvaluator (SquareSampleSource.family F) (SquareSampleSource.readers h)
  refine (E.precompose query query_FP).congr (funext fun q => ?_)
  simp only [Function.comp_apply, SeparableBits.squarefreeValue, PrimitivePairBits.coefficient,
    PrincipalCoefficientBits.integerResidue, RationalSubstitution.IntegerBits.coefficientResidue]
  apply congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
  · simp only [query, ScaledQuotientBits.context, pairFst_pair, pairSnd_pair, preparedPolynomial]
  · simp only [query, ScaledQuotientBits.modulus, ScaledQuotientBits.modulusWord,
      pairFst_pair, pairSnd_pair, RationalSubstitution.IntegerBits.mValue]

noncomputable def context (F : Inputs) (q : List Bool) :=
  pair (SquareSampleSource.prepare F (pairFst q)) (BinaryNatCode.encode (SquareSampleSource.selected F q).val)

theorem context_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (context F) :=
  ((SquareSampleSource.prepare_evaluator h).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP _ (bits_mem_FP (SquareSampleSource.selected_unary h)))

lemma context_polynomial (F : Inputs) (q : List Bool) : preparedPolynomial F (context F q) = polynomial F q := by
  unfold preparedPolynomial context
  rw [SquareSampleSource.prepared_coordinate]
  rfl

theorem evaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial F)) := by
  have E := PrimitivePairBits.withContextEvaluator (preparedPolynomial F) (context F)
    (context_evaluator h) (prepared_evaluator h)
  exact E.congr (funext fun q => by
    simp only [PrimitivePairBits.coefficient, Function.comp_apply, context_polynomial])

end LeanCanny.Encoding.SquareSampleSquarefree
