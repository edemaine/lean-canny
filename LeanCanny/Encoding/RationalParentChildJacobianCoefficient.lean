/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildJacobianEntries
public import LeanCanny.Algebra.FixedWidthDeterminantSpace

/-! # Native modular coefficients of the joint Jacobian determinant

The exponent box fits the whole determinant. The existing determinant
backend guards every encoded entry coefficient before the derivative reader
is called. The canonical packet specification is needed only inside the box.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildJacobianCoefficient
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open RationalParentChildSource (Inputs)
open RationalSubstitution.IntegerBits (context selectedDegree mValue context_mem_FP selectedDegree_mem_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildJacobianSource.matrix RationalParentChildJacobianSource.width
  RationalParentChildJacobianSource.degree RationalParentJointSource.degree

noncomputable def integerCoefficient (F : Inputs) (u : List Bool) (r : ℕ) : ℤ :=
  (RationalParentChildJacobianSource.polynomial F u).coeff
    (RationalSubstitution.Indexed.exponentVector (RationalParentChildSource.count F u) (entry (RationalParentChildJacobianSource.width F u) r))

noncomputable def value (F : Inputs) : List Bool → List Bool :=
  (FixedWidthDeterminantBits.family (RationalParentChildSource.count F ∘ context) (RationalParentChildSource.count F ∘ context)
    (RationalParentChildJacobianSource.width F ∘ context) pairSnd selectedDegree
    (fun q => RationalParentChildJacobianSource.matrix F (context q))).value

theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (value F) :=
  FixedWidthDeterminantBits.evaluator (RationalParentChildSource.count F ∘ context) (RationalParentChildSource.count F ∘ context)
    (RationalParentChildJacobianSource.width F ∘ context) pairSnd selectedDegree
    (fun q => RationalParentChildJacobianSource.matrix F (context q))
    (RationalParentChildJacobianEntries.value F context
      (RationalParentChildJacobianSource.width F ∘ context) pairSnd)
    (RationalParentJointSource.degree F.joint ∘ context)
    (fun q => RationalParentChildJacobianSource.entry_degree F (context q))
    (fun q => RationalParentChildJacobianSource.source_degree_lt_width F (context q))
    (RationalParentChildJacobianEntries.packet F context _ pairSnd)
    (RationalParentChildJacobianEntries.evaluator h context_mem_FP
      ((RationalParentChildJacobianSource.width_unary h).comp context_mem_FP) pairSnd_mem_FP)
    ((RationalParentChildSource.count_unary h).comp context_mem_FP)
    ((RationalParentChildSource.count_unary h).comp context_mem_FP)
    ((RationalParentChildJacobianSource.width_unary h).comp context_mem_FP) pairSnd_mem_FP selectedDegree_mem_FP

theorem value_eq (F : Inputs) (q : List Bool)
    (hr : Nat.fromBitsLE (selectedDegree q) <
      count (RationalParentChildSource.count F (context q)) (RationalParentChildJacobianSource.width F (context q))) :
    value F q = residueBits ((integerCoefficient F (context q) (Nat.fromBitsLE (selectedDegree q)) : ℤ) : ZMod (mValue q)) :=
  FixedWidthDeterminantBits.value_eq (RationalParentChildSource.count F ∘ context) (RationalParentChildSource.count F ∘ context)
    (RationalParentChildJacobianSource.width F ∘ context) pairSnd selectedDegree
    (fun q => RationalParentChildJacobianSource.matrix F (context q)) q
    (RationalParentChildJacobianSource.degree F (context q))
    (RationalParentChildJacobianSource.polynomial_degree F (context q))
    (RationalParentChildJacobianSource.degree_lt_width F (context q)) hr

theorem packet (F : Inputs) (u : List Bool) (r m : ℕ) (hm : 0 < m)
    (hr : r < count (RationalParentChildSource.count F u) (RationalParentChildJacobianSource.width F u)) :
    value F (pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits ((integerCoefficient F u r : ℤ) : ZMod m) := by
  generalize hq : pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1)) = q
  have hu : context q = u := by rw [← hq]; simp only [context, pairFst_pair]
  have hd : Nat.fromBitsLE (selectedDegree q) = r := by
    rw [← hq]; simp only [selectedDegree, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hmod : mValue q = m := by
    rw [← hq]; simp only [mValue, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega
  rw [value_eq F q (by rw [hu, hd]; exact hr)]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m)) (by rw [hu, hd]) hmod

end LeanCanny.Encoding.RationalParentChildJacobianCoefficient
