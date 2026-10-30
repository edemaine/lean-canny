/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointValueBounds

/-! # Native trailing factors for frozen endpoint midpoint tests

The lowest nonzero outer coefficient is computed from the actual midpoint
annihilator and its derived height budget. Its parameter polynomial retains
all source costs and is nonzero at every genuinely prepared endpoint source.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointTrailing
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def polynomial (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) :=
  (FlatAffineEndpointValues.family F height index).affine.homogeneous.annihilator

noncomputable def outerBound (F : Inputs) (r : List Bool) : ℕ := FlatAffineEndpointValues.valueDimension F r + 1
noncomputable def innerBound (F : Inputs) (r : List Bool) : ℕ :=
  FlatAffineEndpointValues.valueDimension F r * FlatAffineEndpointValues.coordinateDegree F r

theorem outerBound_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) : BinaryFn (outerBound F) :=
  (FlatAffineEndpointValues.valueDimension_binary h height index).add (BinaryFn.const 1)

theorem innerBound_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) : BinaryFn (innerBound F) :=
  (FlatAffineEndpointValues.valueDimension_binary h height index).mul (FlatAffineEndpointValues.coordinateDegree_binary h height)

theorem indexEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (index : (r : List Bool) → Fin (count F (pairFst r)))
    (hi : UnaryFn (fun r => (index r).val)) : SpaceFunction (PolynomialTrailingCoefficientBits.index (polynomial F height index)) :=
  PolynomialTrailingCoefficientBits.index_evaluator _ (FlatAffineEndpointValues.reader h height hh index hi)
    (outerBound_binary h height index) (innerBound_binary h height index)
    (FlatAffineEndpointValueBounds.heightBound_binary h height index)
    (FlatAffineEndpointValues.degree_le F height index) (FlatAffineEndpointValues.parameter_degree_le F height index)
    (FlatAffineEndpointValueBounds.height_le F height index)

theorem valueEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (index : (r : List Bool) → Fin (count F (pairFst r)))
    (hi : UnaryFn (fun r => (index r).val)) : SpaceFunction (PolynomialTrailingCoefficientBits.value (polynomial F height index)) :=
  PolynomialTrailingCoefficientBits.evaluator _ (FlatAffineEndpointValues.reader h height hh index hi)
    (outerBound_binary h height index) (innerBound_binary h height index)
    (FlatAffineEndpointValueBounds.heightBound_binary h height index)
    (FlatAffineEndpointValues.degree_le F height index) (FlatAffineEndpointValues.parameter_degree_le F height index)
    (FlatAffineEndpointValueBounds.height_le F height index)

def primitiveQuery (q : List Bool) : List Bool := pair (pair (pairFst (pairFst q)) (pairSnd q)) (pairSnd (pairFst q))
theorem primitiveQuery_FP : primitiveQuery ∈ FP := by polytime [primitiveQuery]

theorem coefficientEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (index : (r : List Bool) → Fin (count F (pairFst r)))
    (hi : UnaryFn (fun r => (index r).val)) : SpaceFunction (PrimitivePairBits.coefficient
      (fun r => (polynomial F height index r).trailingCoeff)) := by
  refine ((valueEvaluator h height hh index hi).precompose primitiveQuery primitiveQuery_FP).congr (funext fun q => ?_)
  let read (r k m : List Bool) := residueBits (((polynomial F height index r).trailingCoeff.coeff (Nat.fromBitsLE k)) :
    ZMod (Nat.fromBitsLE m + 1))
  change read (pairFst (pairFst (primitiveQuery q))) (pairSnd (primitiveQuery q)) (pairSnd (pairFst (primitiveQuery q))) =
    read (pairFst (pairFst q)) (pairSnd (pairFst q)) (pairSnd q)
  simp only [primitiveQuery, pairFst_pair, pairSnd_pair]

theorem ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (index : (r : List Bool) → Fin (count F (pairFst r)))
    (u : List Bool) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height u) = 0) :
    (polynomial F height index (FlatAffineEndpointPreparation.record F height u)).trailingCoeff ≠ 0 :=
  Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (FlatAffineEndpointValues.ne_zero F hcone height index u a ha)

theorem degree_le (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) (r : List Bool) :
    (polynomial F height index r).trailingCoeff.natDegree ≤ innerBound F r :=
  FlatAffineEndpointValues.parameter_degree_le F height index r (polynomial F height index r).natTrailingDegree

end LeanCanny.Encoding.FlatAffineEndpointTrailing
