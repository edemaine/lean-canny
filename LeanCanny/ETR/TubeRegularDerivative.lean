/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularSource
public import LeanCanny.Algebra.ReciprocalSpace

/-! # The original base-partial coefficient evaluator for reciprocal regularity

The existing projection-term machine already computes the embedded derivative
of the level row. Its one source call, binary derivative factor, direction
pattern guards and all child costs are reused without a new derivative oracle.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularDerivative
open Complexity LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding TubeProjectionEncoding
open LeanCanny.Algebra LeanCanny.Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubePolynomial.integerProjection
  TubePolynomial.integerPolynomial TubeDense.polynomial TubeProjectionQuery.termValue

theorem term_derivative_level (n : ℕ) (p : MvPolynomial (Fin n) ℤ) (s : Finset (Constraint n)) :
    TubeProjectionQuery.termPolynomial n (TubePolynomial.integerPolynomial p s)
      (.inl (TubePolynomial.base (Fin n))) none true =
      MvPolynomial.pderiv (TubeRegularSource.base n) (TubePolynomial.integerProjection p s none) := by
  rw [TubeProjectionQuery.integerProjection_level_term]
  simp only [TubeProjectionQuery.termPolynomial, Bool.false_eq_true, ite_false, ite_true,
    TubeProjectionQuery.shiftVector, MvPolynomial.monomial_zero', map_one, mul_one]
  exact (MvPolynomial.pderiv_rename ProjectionFlatten.coefficientEmbedding_injective _ _).symm

noncomputable def derivativeAt (source active modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) : List Bool :=
  residueBits (((MvPolynomial.pderiv (TubeRegularSource.base (CompactSource.term (source c)).arity)
    (TubeSource.integerProjection (source c) (activeSet (TubeIndexed.arity (source c)) (active c)) none)).coeff
      (FixedWidthPolynomial.nativeExponent (variableEquiv (TubeIndexed.arity (source c)))
        (TubeIndexed.blockWidth (source c)) r) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

noncomputable def derivativeResidue (source active modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  derivativeAt source active modulus (pairFst q) (Nat.fromBitsLE (pairSnd q))

theorem termValue_eq (source active modulus : List Bool → List Bool) (q : List Bool) :
    TubeProjectionQuery.termValue (TubeIndexed.compiled source ∘ pairFst)
      (TubeIndexed.blockWidth ∘ source ∘ pairFst) (active ∘ pairFst) FixedWidthPolynomial.rankTarget (modulus ∘ pairFst)
      true (fun c => .inl (TubePolynomial.base (Fin (TubeDense.arity (TubeIndexed.compiled source ∘ pairFst) c))))
      (fun _ => none) q = derivativeResidue source active modulus q := by
  let b := TubeIndexed.compiled source ∘ pairFst
  let W := TubeIndexed.blockWidth ∘ source ∘ pairFst
  let n := TubeDense.arity b
  unfold TubeProjectionQuery.termValue derivativeResidue derivativeAt
  rw [term_derivative_level]
  have he : TubeProjectionQuery.exponent n W FixedWidthPolynomial.rankTarget q =
      FixedWidthPolynomial.nativeExponent (variableEquiv (TubeIndexed.arity (source (pairFst q))))
        (TubeIndexed.blockWidth (source (pairFst q))) (Nat.fromBitsLE (pairSnd q)) := by
    dsimp +instances only [n, b, TubeDense.arity, TermArity.arity, TubeIndexed.compiled, TubeIndexed.arity, CompactSource.term]
    ext j
    simp only [TubeProjectionQuery.exponent, Finsupp.coe_equivFunOnFinite_symm, FixedWidthQuery.coordinate,
      W, Function.comp_apply, FixedWidthPolynomial.rankTarget, BinaryNat.normalize_eq_bits,
      FixedWidthPolynomial.nativeExponent, FixedWidthPolynomial.entry]
    rfl
  rw [he]
  dsimp +instances only [n, b, TubeDense.polynomial, TubeDense.arity, TermArity.arity, TubeIndexed.compiled,
    TubeSource.integerProjection, CompactSource.polynomial, CompactSource.term, TubeIndexed.arity, Function.comp_apply]
  unfold TubeDense.polynomial
  simp +instances only [Function.comp_apply]

noncomputable def termEvaluator (b : List Bool → List Bool) (W : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (hb : b ∈ FP) (hW : UnaryFn W)
    (ha : active ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (TubeProjectionQuery.termValue b W active target modulus true
      (fun q => .inl (TubePolynomial.base (Fin (TubeDense.arity b q)))) (fun _ => none)) := by
  let n := TubeDense.arity b
  exact TubeProjectionQuery.termEvaluator b W n n active target modulus true false
    (fun q => .inl (TubePolynomial.base (Fin (n q)))) (fun _ => none)
    hb hW (TubeDense.arity_unary hb) (TubeDense.arity_unary hb) ha ht hm
    (fun q => (index_shift_source_false (n q)).symm) (fun _ => rfl)

noncomputable def evaluator (source active modulus : List Bool → List Bool)
    (hs : source ∈ FP) (ha : active ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (derivativeResidue source active modulus) := by
  have hb := mem_FP_comp pairFst_mem_FP (TubeIndexed.compiled_mem_FP hs)
  have hW := (TubeIndexed.blockWidth_unary.comp hs).comp pairFst_mem_FP
  have E := termEvaluator (TubeIndexed.compiled source ∘ pairFst)
    (TubeIndexed.blockWidth ∘ source ∘ pairFst) (active ∘ pairFst) FixedWidthPolynomial.rankTarget
    (modulus ∘ pairFst) hb hW (mem_FP_comp pairFst_mem_FP ha)
    FixedWidthPolynomial.rankTarget_mem_FP (mem_FP_comp pairFst_mem_FP hm)
  exact E.congr (funext (termValue_eq source active modulus))

theorem derivative_packet (source active modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    derivativeResidue source active modulus (pair c (BinaryNatCode.encode r)) = residueBits
      (((MvPolynomial.pderiv (TubeRegularSource.base (CompactSource.term (source c)).arity)
        (TubeSource.integerProjection (source c) (activeSet (TubeIndexed.arity (source c)) (active c)) none)).coeff
        (FixedWidthPolynomial.nativeExponent (variableEquiv (TubeIndexed.arity (source c)))
          (TubeIndexed.blockWidth (source c)) r) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  change derivativeAt source active modulus (pairFst (pair c (BinaryNatCode.encode r)))
    (Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode r)))) = _
  rw [pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
  rfl

end LeanCanny.ETR.TubeRegularDerivative
