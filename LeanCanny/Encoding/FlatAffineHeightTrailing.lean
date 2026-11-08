/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineHeightValueBounds
public import LeanCanny.Algebra.PolynomialTrailingCoefficientSpace

/-! # Native trailing factors of actual affine-height value certificates

Outer and parameter degree bounds and integer coefficient-height budgets are
derived from the original source. The native lowest-nonzero-coefficient scan
then computes the actual trailing factor. Its index is not a reader premise.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineHeightTrailing
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical

noncomputable def polynomial (F : Inputs) (height row : (u : List Bool) → Fin (count F u)) :=
  (FlatAffineHeightValues.family F height row).affine.homogeneous.annihilator

noncomputable def outerBound (F : Inputs) (row : (u : List Bool) → Fin (count F u)) (u : List Bool) :=
  FlatAffineHeightValues.valueDimension F row u + 1

noncomputable def innerBound (F : Inputs) (row : (u : List Bool) → Fin (count F u)) (u : List Bool) :=
  FlatAffineHeightValues.valueDimension F row u * FlatAffineHeightValues.coordinateDegree F u

theorem outerBound_binary {F : Inputs} (h : F.Access) (height row : (u : List Bool) → Fin (count F u))
    (hr : UnaryFn (fun u => (row u).val)) : BinaryFn (outerBound F row) :=
  (FlatAffineHeightValues.valueDimension_binary h height row hr).add (BinaryFn.const 1)

theorem innerBound_binary {F : Inputs} (h : F.Access) (height row : (u : List Bool) → Fin (count F u))
    (hr : UnaryFn (fun u => (row u).val)) : BinaryFn (innerBound F row) :=
  (FlatAffineHeightValues.valueDimension_binary h height row hr).mul (FlatAffineHeightValues.coordinateDegree_binary h)

theorem indexEvaluator {F : Inputs} (h : F.Access) (height row : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (hr : UnaryFn (fun u => (row u).val)) :
    SpaceFunction (PolynomialTrailingCoefficientBits.index (polynomial F height row)) :=
  PolynomialTrailingCoefficientBits.index_evaluator _ (FlatAffineHeightValues.reader h height row hh hr)
    (outerBound_binary h height row hr) (innerBound_binary h height row hr)
    (FlatAffineHeightValueBounds.heightBound_binary h height row hr)
    (FlatAffineHeightValues.degree_le F height row) (FlatAffineHeightValues.parameter_degree_le F height row)
    (FlatAffineHeightValueBounds.height_le F height row)

theorem valueEvaluator {F : Inputs} (h : F.Access) (height row : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (hr : UnaryFn (fun u => (row u).val)) :
    SpaceFunction (PolynomialTrailingCoefficientBits.value (polynomial F height row)) :=
  PolynomialTrailingCoefficientBits.evaluator _ (FlatAffineHeightValues.reader h height row hh hr)
    (outerBound_binary h height row hr) (innerBound_binary h height row hr)
    (FlatAffineHeightValueBounds.heightBound_binary h height row hr)
    (FlatAffineHeightValues.degree_le F height row) (FlatAffineHeightValues.parameter_degree_le F height row)
    (FlatAffineHeightValueBounds.height_le F height row)

def primitiveQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairSnd q)) (pairSnd (pairFst q))

theorem primitiveQuery_FP : primitiveQuery ∈ FP := mem_FP_pair
  (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

/-- Standard univariate modular access to the actual trailing polynomial,
suitable for the streamed exceptional-factor product and root algorithms. -/
theorem coefficientEvaluator {F : Inputs} (h : F.Access) (height row : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (hr : UnaryFn (fun u => (row u).val)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun u => (polynomial F height row u).trailingCoeff)) := by
  refine ((valueEvaluator h height row hh hr).precompose primitiveQuery primitiveQuery_FP).congr (funext fun q => ?_)
  let read (c k m : List Bool) := residueBits (((polynomial F height row c).trailingCoeff.coeff
    (Nat.fromBitsLE k)) : ZMod (Nat.fromBitsLE m + 1))
  change read (pairFst (pairFst (primitiveQuery q))) (pairSnd (primitiveQuery q))
      (pairSnd (pairFst (primitiveQuery q))) =
    read (pairFst (pairFst q)) (pairSnd (pairFst q)) (pairSnd q)
  simp only [primitiveQuery, pairFst_pair, pairSnd_pair]

theorem trailing_ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height row : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    (polynomial F height row u).trailingCoeff ≠ 0 :=
  Polynomial.trailingCoeff_ne_zero.mpr (FlatAffineHeightValues.ne_zero F hcone height row u)

theorem trailing_degree_le (F : Inputs) (height row : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    (polynomial F height row u).trailingCoeff.natDegree ≤ innerBound F row u :=
  FlatAffineHeightValues.parameter_degree_le F height row u (polynomial F height row u).natTrailingDegree

end LeanCanny.Encoding.FlatAffineHeightTrailing
