/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleIndexedSign

/-! # Native indexed derivative signs at flat sample descriptors -/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleDerivativeSigns
open LeanCanny.Algebra LeanCanny.Computation
open FlatFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceSampleCoordinates.parameter FlatFullSourceSampleCoordinates.coordinate
  PrimitivePairBits.coefficient FlatFullSourceSampleCoordinates.parameterDegree FlatFullSourceSampleCoordinates.baseHeight
  FlatFullSourceSampleThom.polynomial FlatFullSourceSampleThom.massExponent

noncomputable def currentTest (F : Inputs) : FlatFullSourceSampleTestMoments.Test where
  polynomial w := FlatFullSourceSampleThom.polynomial F (pairFst w) (Nat.fromBitsLE (pairSnd w))
  degree w := FlatFullSourceSampleCoordinates.parameterDegree F (pairFst w)
  mass w := FlatFullSourceSampleThom.massExponent F (pairFst w)
  polynomial_degree w := FlatFullSourceSampleThom.degree F (pairFst w) _
  polynomial_mass w := FlatFullSourceSampleThom.mass_bound F (pairFst w) _

def derivativeQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (RationalSubstitution.IntegerBits.context q))
    (pair (pairSnd (RationalSubstitution.IntegerBits.context q)) (RationalSubstitution.IntegerBits.selectedDegree q))) (pairSnd q)

theorem derivativeQuery_FP : derivativeQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
      RationalSubstitution.IntegerBits.selectedDegree_mem_FP)) pairSnd_mem_FP

noncomputable def currentAccess {F : Inputs} (h : F.Access) : (currentTest F).Access := by
  have hd : BinaryFn (currentTest F).degree :=
    (FlatFullSourceSampleCoordinates.parameterDegree_binary h).comp pairFst_mem_FP
  have hm : BinaryFn (currentTest F).mass :=
    (FlatFullSourceSampleThom.massExponent_binary h).comp pairFst_mem_FP
  apply FlatFullSourceSampleTestMoments.Test.Access.ofPrimitive (T := currentTest F) hd hm
  have E := (FlatFullSourceSampleThom.evaluator h).precompose derivativeQuery derivativeQuery_FP
  refine E.congr ?_
  funext q
  simp only [Function.comp_apply, FlatFullSourceSampleThom.value, PrimitivePairBits.coefficient,
    RationalSubstitution.IntegerBits.coefficientResidue, currentTest]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => MatrixPower.residueBits (z : ZMod m))
    (by simp only [derivativeQuery, FlatFullSourceSampleThom.original, FlatFullSourceSampleThom.order,
      FlatFullSourceSampleThom.index, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair])
    (by simp only [derivativeQuery, RationalSubstitution.IntegerBits.mValue, pairSnd_pair])

noncomputable def currentValue (F : Inputs) : List Bool → List Bool :=
  FlatFullSourceSampleIndexedSign.value F (currentTest F)

theorem current_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (currentValue F) :=
  FlatFullSourceSampleIndexedSign.evaluator h (currentAccess h)

theorem current_packet (F : Inputs) (u : List Bool) (x : FlatFullSourceSampleRecordSpan.Root F u) (k : ℕ) :
    currentValue F (pair (pair u (FlatFullSourceSampleHashChoice.descriptor F u x)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign
        ((FlatFullSourceSampleThom.polynomial F u k).eval₂ (Int.castRingHom ℝ) x.val)) := by
  rw [currentValue, FlatFullSourceSampleIndexedSign.value_descriptor]
  simp only [FlatFullSourceSampleTestMoments.sign, currentTest, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Polynomial.eval_map]


end LeanCanny.Encoding.FlatFullSourceSampleDerivativeSigns
