/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentBlockCodes
public import LeanCanny.Encoding.BoundedFullCoefficient
public import LeanCanny.Algebra.FixedWidthRationalSubstitutionSpace

/-! # Full-source blocks over native rational parent families

The parent may be a derived child family. Dense source coefficients and all
parent-coordinate computations are charged by the native substitution engine.
The source is streamed without expansion into term syntax. Fixed even
clearing exponents and all degree controls are derived from the two families.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentFullBlock
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair pairFst pairSnd BoundedFullCoefficient.valueData

structure Inputs where
  parent : RationalCoordinateFamily.Family
  source : Readers
  offset : List Bool → ℕ
  dim : List Bool → ℕ

structure Inputs.Access (F : Inputs) : Prop where
  parent : RationalCoordinateFamily.Access F.parent
  source : F.source.PolyTime
  offset : BinaryFn F.offset
  dim : UnaryFn F.dim

def arity (F : Inputs) (u : List Bool) : ℕ := F.source.dim u + 4
noncomputable def sourceWidth (F : Inputs) (u : List Bool) : ℕ := (degree F.source u).size
noncomputable def grid (F : Inputs) (u : List Bool) : ℕ := 2 ^ sourceWidth F u
noncomputable def clearing (F : Inputs) (u : List Bool) : ℕ := 2 * grid F u
noncomputable def extent (F : Inputs) (u : List Bool) : ℕ :=
  max (F.parent.degree u) 1
noncomputable def degreeBound (F : Inputs) (u : List Bool) : ℕ := arity F u * clearing F u * extent F u
noncomputable def width (F : Inputs) (u : List Bool) : ℕ := (degreeBound F u + extent F u + 1).size
noncomputable def span (F : Inputs) (u : List Bool) : ℕ := width F u * (F.dim u + 1)

theorem degreeBound_pos (F : Inputs) (u : List Bool) : 0 < degreeBound F u := by
  unfold degreeBound arity clearing grid extent
  positivity

theorem arity_unary {F : Inputs} (h : F.Access) : UnaryFn (arity F) := h.source.dim.add (UnaryFn.const 4)
theorem sourceWidth_unary {F : Inputs} (h : F.Access) : UnaryFn (sourceWidth F) :=
  (UnaryFn.length (degree_binary h.source).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
theorem grid_binary {F : Inputs} (h : F.Access) : BinaryFn (grid F) :=
  (BinaryFn.const 2).powUnary (sourceWidth_unary h)
theorem clearing_binary {F : Inputs} (h : F.Access) : BinaryFn (clearing F) :=
  (BinaryFn.const 2).mul (grid_binary h)
theorem extent_binary {F : Inputs} (h : F.Access) : BinaryFn (extent F) :=
  BivariateRationalTermReader.max_binary
    h.parent.degree (BinaryFn.const 1)
theorem degreeBound_binary {F : Inputs} (h : F.Access) : BinaryFn (degreeBound F) :=
  ((BinaryFn.ofUnary (arity_unary h)).mul (clearing_binary h)).mul (extent_binary h)
theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  (UnaryFn.length (((degreeBound_binary h).add (extent_binary h)).add (BinaryFn.const 1)).bits_mem_FP).of_eq
    (fun _ => BinaryNatCode.length_encode _)
theorem span_unary {F : Inputs} (h : F.Access) : UnaryFn (span F) :=
  (width_unary h).mul (h.dim.add (UnaryFn.const 1))

theorem extent_lt (F : Inputs) (u : List Bool) : extent F u < 2 ^ width F u :=
  (by omega : extent F u ≤ degreeBound F u + extent F u + 1).trans_lt (Nat.lt_size_self _)
theorem degree_lt (F : Inputs) (u : List Bool) : degreeBound F u < 2 ^ width F u :=
  (by omega : degreeBound F u ≤ degreeBound F u + extent F u + 1).trans_lt (Nat.lt_size_self _)

noncomputable def family (F : Inputs) : FixedWidthRationalSubstitutionBits.Family where
  arity := arity F
  width := sourceWidth F
  source := BoundedFullCriticalSamples.polynomial F.source
  numerator := RationalParentBlockCodes.encoded F.parent (width F) F.offset F.dim true
  denominator := RationalParentBlockCodes.encoded F.parent (width F) F.offset F.dim false
  degree_fit u i := (degreeOf_le_totalDegree _ i).trans_lt
    ((BoundedFullCriticalSamples.source_degree F.source u).trans_lt (Nat.lt_size_self _))

noncomputable def sourceCoefficient (F : Inputs) : List Bool → List Bool :=
  BoundedFullCoefficient.value (F.source.comp RationalSubstitution.IntegerBits.context)
    (sourceWidth F ∘ RationalSubstitution.IntegerBits.context) RationalSubstitution.IntegerBits.selectedDegree pairSnd

theorem sourceCoefficient_evaluator {F : Inputs} (h : F.Access)
    (ht : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) : SpaceFunction (sourceCoefficient F) :=
  BoundedFullCoefficient.evaluator (h.source.comp RationalSubstitution.IntegerBits.context_mem_FP)
    ((sourceWidth_unary h).comp RationalSubstitution.IntegerBits.context_mem_FP)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
    (fun q => ht (RationalSubstitution.IntegerBits.context q))

theorem sourceCoefficient_packet (F : Inputs) (u : List Bool) (r m : ℕ) (hm : 0 < m) :
    sourceCoefficient F (pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits ((((family F).coefficient u r : ℤ)) : ZMod m) := by
  unfold sourceCoefficient
  rw [BoundedFullCoefficient.value_data]
  simp only [Readers.comp, Function.comp_apply, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair]
  rw [← BoundedFullCoefficient.value_data F.source (sourceWidth F) (fun _ => BinaryNatCode.encode r)
    (fun _ => BinaryNatCode.encode (m - 1)) u]
  unfold BoundedFullCoefficient.value FixedWidthRationalSubstitutionBits.Family.coefficient
  apply congrArg₂ (fun (z : ℤ) (n : ℕ) => MatrixPower.residueBits (z : ZMod n))
  · rfl
  · simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]

noncomputable def access {F : Inputs} (h : F.Access)
    (htS : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) :
    FixedWidthRationalSubstitutionBits.Access (family F) where
  arity := arity_unary h
  width := sourceWidth_unary h
  coefficient := sourceCoefficient F
  evaluator := sourceCoefficient_evaluator h htS
  coefficient_eq u r _ m hm := sourceCoefficient_packet F u r m hm
  coordinates := RationalParentBlockCodes.readers h.parent (width_unary h) h.offset h.dim (arity F)

theorem evaluator {F : Inputs} (h : F.Access)
    (htS : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) :
    SpaceFunction (PrimitivePairBits.coefficient (family F).polynomial) :=
  (access h htS).polynomialEvaluator

end LeanCanny.Encoding.RationalParentFullBlock
