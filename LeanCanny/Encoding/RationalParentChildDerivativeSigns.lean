/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildIndexedSign
public import LeanCanny.Encoding.RationalParentChildParentThom
public import LeanCanny.Encoding.RationalParentChildParents

/-! # Native retained-parent and child-parameter derivative signs -/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildDerivativeSigns
open LeanCanny.Algebra LeanCanny.Computation
open RationalParentChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildCoordinates.parameter RationalParentChildCoordinates.coordinate
  RationalParentChildParentThom.polynomial RationalParentChildParentThom.degree RationalParentChildParentThom.mass
  PrimitivePairBits.coefficient RationalParentChildCoordinates.parameterDegree RationalParentChildCoordinates.baseHeight
  RationalParentChildThom.polynomial RationalParentChildThom.massExponent

noncomputable def parentTest (F : Inputs) : RationalParentChildTestMoments.Test where
  polynomial := RationalParentChildParentThom.polynomial F
  degree := RationalParentChildParentThom.degree F
  mass := RationalParentChildParentThom.mass F
  polynomial_degree := RationalParentChildParentThom.polynomial_degree F
  polynomial_mass := RationalParentChildParentThom.polynomial_mass F

noncomputable def parentAccess {F : Inputs} (h : F.Access) : (parentTest F).Access :=
  RationalParentChildTestMoments.Test.Access.ofPrimitive
    (RationalParentChildParentThom.degree_binary h) (RationalParentChildParentThom.mass_binary h)
    (RationalParentChildParentThom.evaluator h)

noncomputable def parentValue (F : Inputs) : List Bool → List Bool :=
  RationalParentChildIndexedSign.value F (parentTest F)

theorem parent_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (parentValue F) :=
  RationalParentChildIndexedSign.evaluator h (parentAccess h)

theorem parent_packet (F : Inputs) (u : List Bool) (x : RationalParentChildRecordSpan.Root F u) (k : ℕ) :
    parentValue F (pair (pair u (RationalParentChildHashChoice.descriptor F u x)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign ((SeparablePolynomialThom.polynomial F.joint.parent u k).eval₂
        (Int.castRingHom ℝ) (RationalParentChildParameters.decode F u x.val (RationalParentChildParentThom.first F u)))) := by
  rw [parentValue, RationalParentChildIndexedSign.value_descriptor]
  simp only [RationalParentChildTestMoments.sign, parentTest, Polynomial.eval_map]
  rw [RationalParentChildParentThom.sign F u k x.val
    ((RationalParentChildQueries.mem_roots F u x.val).mp x.property).1]

noncomputable def currentTest (F : Inputs) : RationalParentChildTestMoments.Test where
  polynomial w := RationalParentChildThom.polynomial F (pairFst w) (Nat.fromBitsLE (pairSnd w))
  degree w := RationalParentChildCoordinates.parameterDegree F (pairFst w)
  mass w := RationalParentChildThom.massExponent F (pairFst w)
  polynomial_degree w := RationalParentChildThom.degree F (pairFst w) _
  polynomial_mass w := RationalParentChildThom.mass_bound F (pairFst w) _

def derivativeQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (RationalSubstitution.IntegerBits.context q))
    (pair (pairSnd (RationalSubstitution.IntegerBits.context q)) (RationalSubstitution.IntegerBits.selectedDegree q))) (pairSnd q)

theorem derivativeQuery_FP : derivativeQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
      RationalSubstitution.IntegerBits.selectedDegree_mem_FP)) pairSnd_mem_FP

noncomputable def currentAccess {F : Inputs} (h : F.Access) : (currentTest F).Access := by
  have hd : BinaryFn (currentTest F).degree :=
    (RationalParentChildCoordinates.parameterDegree_binary h).comp pairFst_mem_FP
  have hm : BinaryFn (currentTest F).mass :=
    (RationalParentChildThom.massExponent_binary h).comp pairFst_mem_FP
  apply RationalParentChildTestMoments.Test.Access.ofPrimitive (T := currentTest F) hd hm
  have E := (RationalParentChildThom.evaluator h).precompose derivativeQuery derivativeQuery_FP
  refine E.congr ?_
  funext q
  simp only [Function.comp_apply, RationalParentChildThom.value, PrimitivePairBits.coefficient,
    RationalSubstitution.IntegerBits.coefficientResidue, currentTest]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => MatrixPower.residueBits (z : ZMod m))
    (by simp only [derivativeQuery, RationalParentChildThom.original, RationalParentChildThom.order,
      RationalParentChildThom.index, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair])
    (by simp only [derivativeQuery, RationalSubstitution.IntegerBits.mValue, pairSnd_pair])

noncomputable def currentValue (F : Inputs) : List Bool → List Bool :=
  RationalParentChildIndexedSign.value F (currentTest F)

theorem current_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (currentValue F) :=
  RationalParentChildIndexedSign.evaluator h (currentAccess h)

theorem current_packet (F : Inputs) (u : List Bool) (x : RationalParentChildRecordSpan.Root F u) (k : ℕ) :
    currentValue F (pair (pair u (RationalParentChildHashChoice.descriptor F u x)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign
        ((SeparablePolynomialThom.polynomial (RationalParentChildParents.parameter F) u k).eval₂ (Int.castRingHom ℝ) x.val)) := by
  rw [currentValue, RationalParentChildIndexedSign.value_descriptor]
  simp only [RationalParentChildTestMoments.sign, currentTest, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Polynomial.eval_map]
  unfold SeparablePolynomialThom.polynomial RationalParentChildThom.polynomial RationalParentChildParents.parameter
  rfl

end LeanCanny.Encoding.RationalParentChildDerivativeSigns
