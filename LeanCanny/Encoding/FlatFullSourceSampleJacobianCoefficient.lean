/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleJacobianEntries
public import LeanCanny.Algebra.FixedWidthDeterminantSpace

/-! # Native modular coefficients of the complete flat Jacobian determinant

The exponent box fits the whole determinant. The existing determinant
backend guards every encoded entry coefficient before the derivative reader
is called. The canonical packet specification is needed only inside the box.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleJacobianCoefficient
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FlatFullSourceTower (Inputs)
open RationalSubstitution.IntegerBits (context selectedDegree mValue context_mem_FP selectedDegree_mem_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceSampleJacobianSource.matrix FlatFullSourceSampleJacobianSource.width
  FlatFullSourceSampleJacobianSource.degree FlatFullSourceTower.degree

noncomputable def integerCoefficient (F : Inputs) (u : List Bool) (r : ℕ) : ℤ :=
  (FlatFullSourceSampleJacobianSource.polynomial F u).coeff
    (RationalSubstitution.Indexed.exponentVector (FlatFullSourceSampleSource.count F u) (entry (FlatFullSourceSampleJacobianSource.width F u) r))

noncomputable def value (F : Inputs) : List Bool → List Bool :=
  (FixedWidthDeterminantBits.family (FlatFullSourceSampleSource.count F ∘ context) (FlatFullSourceSampleSource.count F ∘ context)
    (FlatFullSourceSampleJacobianSource.width F ∘ context) pairSnd selectedDegree
    (fun q => FlatFullSourceSampleJacobianSource.matrix F (context q))).value

theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (value F) :=
  FixedWidthDeterminantBits.evaluator (FlatFullSourceSampleSource.count F ∘ context) (FlatFullSourceSampleSource.count F ∘ context)
    (FlatFullSourceSampleJacobianSource.width F ∘ context) pairSnd selectedDegree
    (fun q => FlatFullSourceSampleJacobianSource.matrix F (context q))
    (FlatFullSourceSampleJacobianEntries.value F context
      (FlatFullSourceSampleJacobianSource.width F ∘ context) pairSnd)
    (FlatFullSourceTower.degree F ∘ context)
    (fun q => FlatFullSourceSampleJacobianSource.entry_degree F (context q))
    (fun q => FlatFullSourceSampleJacobianSource.source_degree_lt_width F (context q))
    (FlatFullSourceSampleJacobianEntries.packet F context _ pairSnd)
    (FlatFullSourceSampleJacobianEntries.evaluator h context_mem_FP
      ((FlatFullSourceSampleJacobianSource.width_unary h).comp context_mem_FP) pairSnd_mem_FP)
    ((FlatFullSourceSampleSource.count_unary h).comp context_mem_FP)
    ((FlatFullSourceSampleSource.count_unary h).comp context_mem_FP)
    ((FlatFullSourceSampleJacobianSource.width_unary h).comp context_mem_FP) pairSnd_mem_FP selectedDegree_mem_FP

theorem value_eq (F : Inputs) (q : List Bool)
    (hr : Nat.fromBitsLE (selectedDegree q) <
      count (FlatFullSourceSampleSource.count F (context q)) (FlatFullSourceSampleJacobianSource.width F (context q))) :
    value F q = residueBits ((integerCoefficient F (context q) (Nat.fromBitsLE (selectedDegree q)) : ℤ) : ZMod (mValue q)) :=
  FixedWidthDeterminantBits.value_eq (FlatFullSourceSampleSource.count F ∘ context) (FlatFullSourceSampleSource.count F ∘ context)
    (FlatFullSourceSampleJacobianSource.width F ∘ context) pairSnd selectedDegree
    (fun q => FlatFullSourceSampleJacobianSource.matrix F (context q)) q
    (FlatFullSourceSampleJacobianSource.degree F (context q))
    (FlatFullSourceSampleJacobianSource.polynomial_degree F (context q))
    (FlatFullSourceSampleJacobianSource.degree_lt_width F (context q)) hr

theorem packet (F : Inputs) (u : List Bool) (r m : ℕ) (hm : 0 < m)
    (hr : r < count (FlatFullSourceSampleSource.count F u) (FlatFullSourceSampleJacobianSource.width F u)) :
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

end LeanCanny.Encoding.FlatFullSourceSampleJacobianCoefficient
