/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleIndexedSign

/-! # Native indexed derivative signs at square-system sample descriptors -/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleDerivativeSigns
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SquareSampleCoordinates.parameter SquareSampleCoordinates.coordinate
  PrimitivePairBits.coefficient SquareSampleCoordinates.parameterDegree SquareSampleCoordinates.baseHeight
  SquareSampleThom.polynomial SquareSampleThom.massExponent

noncomputable def currentTest (F : Inputs) : SquareSampleTestMoments.Test where
  polynomial w := SquareSampleThom.polynomial F (pairFst w) (Nat.fromBitsLE (pairSnd w))
  degree w := SquareSampleCoordinates.parameterDegree F (pairFst w)
  mass w := SquareSampleThom.massExponent F (pairFst w)
  polynomial_degree w := SquareSampleThom.degree F (pairFst w) _
  polynomial_mass w := SquareSampleThom.mass_bound F (pairFst w) _

def derivativeQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (RationalSubstitution.IntegerBits.context q))
    (pair (pairSnd (RationalSubstitution.IntegerBits.context q)) (RationalSubstitution.IntegerBits.selectedDegree q))) (pairSnd q)

theorem derivativeQuery_FP : derivativeQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
      RationalSubstitution.IntegerBits.selectedDegree_mem_FP)) pairSnd_mem_FP

noncomputable def currentAccess {F : Inputs} (h : F.Access) : (currentTest F).Access := by
  have hd : BinaryFn (currentTest F).degree :=
    (SquareSampleCoordinates.parameterDegree_binary h).comp pairFst_mem_FP
  have hm : BinaryFn (currentTest F).mass :=
    (SquareSampleThom.massExponent_binary h).comp pairFst_mem_FP
  apply SquareSampleTestMoments.Test.Access.ofPrimitive (T := currentTest F) hd hm
  have E := (SquareSampleThom.evaluator h).precompose derivativeQuery derivativeQuery_FP
  refine E.congr ?_
  funext q
  simp only [Function.comp_apply, SquareSampleThom.value, PrimitivePairBits.coefficient,
    RationalSubstitution.IntegerBits.coefficientResidue, currentTest]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => MatrixPower.residueBits (z : ZMod m))
    (by simp only [derivativeQuery, SquareSampleThom.original, SquareSampleThom.order,
      SquareSampleThom.index, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair])
    (by simp only [derivativeQuery, RationalSubstitution.IntegerBits.mValue, pairSnd_pair])

noncomputable def currentValue (F : Inputs) : List Bool → List Bool :=
  SquareSampleIndexedSign.value F (currentTest F)

theorem current_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (currentValue F) :=
  SquareSampleIndexedSign.evaluator h (currentAccess h)

theorem current_packet (F : Inputs) (u : List Bool) (x : SquareSampleRecordSpan.Root F u) (k : ℕ) :
    currentValue F (pair (pair u (SquareSampleHashChoice.descriptor F u x)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign
        ((SquareSampleThom.polynomial F u k).eval₂ (Int.castRingHom ℝ) x.val)) := by
  rw [currentValue, SquareSampleIndexedSign.value_descriptor]
  simp only [SquareSampleTestMoments.sign, currentTest, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Polynomial.eval_map]


end LeanCanny.Encoding.SquareSampleDerivativeSigns
