/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveSourceSampling
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native binary FP controls for implicit coercive sampling bounds

The Macaulay level is calculated from dimension and degree allowances, without
forming the finite degree family. Binary arithmetic then writes the radius and
penalty exponents themselves. Their powers of two remain implicit.
-/

@[expose] public section
namespace LeanCanny.ETR.CoerciveSourceControls
open LeanCanny.Encoding
open LeanCanny.Algebra
open CoerciveCriticalHomogenization CoerciveCoordinateEliminant CoerciveRadiusBits
open CoerciveSourceSampling
open scoped BigOperators

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

/-- The coordinate row has degree one and each of the n gradient rows has
degree 2D+1, so the Macaulay level is 1+2nD. -/
theorem level_eq (n D : ℕ) : Macaulay.level (finDegree (n := n) D) = n * (2 * D) + 1 := by
  unfold Macaulay.level
  have hs := Equiv.sum_comp (layout (n := n)) (fun j => finDegree D j - 1)
  rw [← hs]
  simp [finDegree, nativeDegree, Fintype.sum_option]

theorem sourceWidth_unary : UnaryFn (fun bits => width (dimension bits) (degreeAllowance bits)) := by
  have hl := (dimension_unary.mul ((UnaryFn.const 2).mul degreeAllowance_unary)).add (UnaryFn.const 1)
  have hd := ((UnaryFn.const 2).mul degreeAllowance_unary).add (UnaryFn.const 1)
  apply (hl.max hd).size.of_eq
  intro bits
  rw [width, level_eq]

theorem sourceColumnExponent_unary :
    UnaryFn (fun bits => columnExponent (dimension bits) (degreeAllowance bits)) :=
  (dimension_unary.add (UnaryFn.const 1)).mul sourceWidth_unary

theorem sourceBudgetExponent_unary :
    UnaryFn (fun bits => budgetExponent (degreeAllowance bits) (massAllowance bits)) :=
  ((degreeAllowance_unary.size).add ((UnaryFn.const 2).mul massAllowance_unary)).add (UnaryFn.const 3)

private theorem unary_binary {f : List Bool → ℕ} (hf : UnaryFn f) : BinaryFn f :=
  BinaryFn.of_bits (bits_mem_FP hf)

theorem sourceColumnBound_binary :
    BinaryFn (fun bits => columnBound (dimension bits) (degreeAllowance bits)) := by
  have h := (BinaryFn.const 2).powUnary sourceColumnExponent_unary
  simpa only [columnBound_eq] using h

/-- A native tidy FP computation writes the exact semantic radius exponent. -/
theorem radiusExponent_binary : BinaryFn radiusExponent :=
  ((sourceColumnBound_binary.mul
    (unary_binary (sourceColumnExponent_unary.add sourceBudgetExponent_unary))).add (BinaryFn.const 1))

/-- A native tidy FP computation writes the exact semantic penalty exponent. -/
theorem penaltyExponent_binary : BinaryFn CoerciveSourceSampling.penaltyExponent :=
  (radiusExponent_binary.mul
    (unary_binary (((UnaryFn.const 2).mul degreeAllowance_unary).add (UnaryFn.const 2)))).add
      (unary_binary dimension_unary.size)

noncomputable def radiusCode (bits : List Bool) : List Bool := BinaryNatCode.encode (radiusExponent bits)
noncomputable def penaltyCode (bits : List Bool) : List Bool :=
  BinaryNatCode.encode (CoerciveSourceSampling.penaltyExponent bits)

theorem radiusCode_mem_FP : radiusCode ∈ FP := radiusExponent_binary.bits_mem_FP
theorem penaltyCode_mem_FP : penaltyCode ∈ FP := penaltyExponent_binary.bits_mem_FP

@[simp] theorem radiusCode_value (bits : List Bool) : Nat.fromBitsLE (radiusCode bits) = radiusExponent bits := by
  simp only [radiusCode, BinaryNatCode.encode, Nat.fromBitsLE_bits]
@[simp] theorem penaltyCode_value (bits : List Bool) :
    Nat.fromBitsLE (penaltyCode bits) = CoerciveSourceSampling.penaltyExponent bits := by
  simp only [penaltyCode, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.ETR.CoerciveSourceControls
