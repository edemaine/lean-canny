/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildIndexedSign
public import LeanCanny.Encoding.BoundedFullSampleChildParentThom
public import LeanCanny.Encoding.BoundedCriticalSampleIndexedSign

/-! # Native parent derivative signs at fixed parent and child descriptors

The binary derivative index changes only the test polynomial. Both routines
keep their respective root sets and descriptor hashes fixed. Child probes
clear denominators with an even exponent, preserving every derivative sign.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildParentSign
open LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter Brackets MatrixPower
open BoundedFullSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildQueries.roots
  BoundedFullSampleChildCoordinates.parameter BoundedFullSampleChildCoordinates.parameterDegree
  BoundedCriticalRationalCoordinates.parameter BoundedCriticalRationalCoordinates.parameterDegree
  BoundedCriticalSampleThom.polynomial BoundedCriticalSampleThom.massExponent
  BoundedFullSampleChildParentThom.polynomial BoundedFullSampleChildParentThom.degree
  BoundedFullSampleChildParentThom.mass PrimitivePairBits.coefficient

noncomputable def childTest (F : Inputs) : BoundedFullSampleChildTestMoments.Test where
  polynomial := BoundedFullSampleChildParentThom.polynomial F
  degree := BoundedFullSampleChildParentThom.degree F
  mass := BoundedFullSampleChildParentThom.mass F
  polynomial_degree := BoundedFullSampleChildParentThom.polynomial_degree F
  polynomial_mass := BoundedFullSampleChildParentThom.polynomial_mass F

noncomputable def childAccess {F : Inputs} (h : F.PolyTime) : (childTest F).Access :=
  BoundedFullSampleChildTestMoments.Test.Access.ofPrimitive
    (BoundedFullSampleChildParentThom.degree_binary h)
    (BoundedFullSampleChildParentThom.mass_binary h)
    (BoundedFullSampleChildParentThom.evaluator h)

noncomputable def childValue (F : Inputs) : List Bool → List Bool :=
  BoundedFullSampleChildIndexedSign.value F (childTest F)

theorem child_evaluator {F : Inputs} (h : F.PolyTime) : SpaceFunction (childValue F) :=
  BoundedFullSampleChildIndexedSign.evaluator h (childAccess h)

theorem child_packet (F : Inputs) (u : List Bool) (x : BoundedFullSampleChildRecordSpan.Root F u) (k : ℕ) :
    childValue F (pair (pair u (BoundedFullSampleChildHashChoice.descriptor F u x)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign
        ((BoundedFullSampleChildParentThom.polynomial F (pair u (BinaryNatCode.encode k))).eval₂
          (Int.castRingHom ℝ) x.val)) := by
  rw [childValue, BoundedFullSampleChildIndexedSign.value_descriptor]
  simp only [BoundedFullSampleChildTestMoments.sign, childTest, Polynomial.eval_map]

theorem child_parent_packet (F : Inputs) (u : List Bool)
    (x : BoundedFullSampleChildRecordSpan.Root F u) (k : ℕ) :
    childValue F (pair (pair u (BoundedFullSampleChildHashChoice.descriptor F u x)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign
        ((BoundedCriticalSampleThom.polynomial F.block.parent (pairFst u) k).eval₂ (Int.castRingHom ℝ)
          (BoundedFullSampleChildParameters.decode F u x.val (BoundedFullSampleChildParentThom.first F u)))) := by
  rw [child_packet, BoundedFullSampleChildParentThom.sign F u k x.val
    ((BoundedFullSampleChildQueries.mem_roots F u x.val).mp x.property).1]

noncomputable def parentTest (P : Readers) : BoundedCriticalSampleTestMoments.Test where
  polynomial := fun w => BoundedCriticalSampleThom.polynomial P (pairFst w) (Nat.fromBitsLE (pairSnd w))
  degree := fun w => BoundedCriticalRationalCoordinates.parameterDegree P (pairFst w)
  mass := fun w => BoundedCriticalSampleThom.massExponent P (pairFst w)
  polynomial_degree w := BoundedCriticalSampleThom.degree P (pairFst w) _
  polynomial_mass w := BoundedCriticalSampleThom.mass_bound P (pairFst w) _

def parentQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (RationalSubstitution.IntegerBits.context q))
    (pair (pairSnd (RationalSubstitution.IntegerBits.context q))
      (RationalSubstitution.IntegerBits.selectedDegree q))) (pairSnd q)

theorem parentQuery_FP : parentQuery ∈ FP := mem_FP_pair
  (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
      RationalSubstitution.IntegerBits.selectedDegree_mem_FP)) pairSnd_mem_FP

noncomputable def parentAccess {F : Inputs} (h : F.PolyTime) : (parentTest F.block.parent).Access := by
  apply BoundedCriticalSampleTestMoments.Test.Access.ofPrimitive
    ((BoundedCriticalRationalCoordinates.parameterDegree_binary h.block.parent).comp pairFst_mem_FP)
    ((BoundedCriticalSampleThom.massExponent_binary h.block.parent).comp pairFst_mem_FP)
  have E := (BoundedCriticalSampleThom.evaluator h.block.parent h.parentArity).precompose parentQuery parentQuery_FP
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, BoundedCriticalSampleThom.value, PrimitivePairBits.coefficient,
    RationalSubstitution.IntegerBits.coefficientResidue, parentTest]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
    (by simp only [parentQuery, BoundedCriticalSampleThom.original, BoundedCriticalSampleThom.order,
      BoundedCriticalSampleThom.index, pairFst_pair, pairSnd_pair])
    (by simp only [parentQuery, pairSnd_pair, RationalSubstitution.IntegerBits.mValue])

noncomputable def parentValue (P : Readers) : List Bool → List Bool :=
  BoundedCriticalSampleIndexedSign.value P (parentTest P)

theorem parent_evaluator {F : Inputs} (h : F.PolyTime) : SpaceFunction (parentValue F.block.parent) :=
  BoundedCriticalSampleIndexedSign.evaluator h.block.parent (parentAccess h) h.parentArity

theorem parent_packet (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) (k : ℕ) :
    parentValue P (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign
        ((BoundedCriticalSampleThom.polynomial P c k).eval₂ (Int.castRingHom ℝ)
          (BoundedCriticalSampleLabels.parameter P c x).val)) := by
  rw [parentValue, BoundedCriticalSampleIndexedSign.value_sample]
  simp only [BoundedCriticalSampleTestMoments.sign, parentTest, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Polynomial.eval_map]

end LeanCanny.Encoding.BoundedFullSampleChildParentSign
