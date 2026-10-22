/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveQueryReaders

/-! # Repacking Macaulay ranks into native source coefficient blocks -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveHomogeneousRepack
open LeanCanny.Encoding LeanCanny.Algebra
open CoerciveSourceSampling
attribute [local irreducible] RationalSubstitutionBits.compiledTerm
attribute [local irreducible] CoerciveSourceSampling.dimension CoercivePowerReaders.size CoercivePowerReaders.width

noncomputable def width (bits : List Bool) : ℕ :=
  CoerciveCoordinateEliminant.width (dimension bits) (degreeAllowance bits)

theorem width_unary : UnaryFn width := CoerciveSourceControls.sourceWidth_unary

theorem width_le (bits : List Bool) : width bits ≤ CoercivePowerReaders.width bits := by
  have h := CoerciveRadiusBits.width_le (dimension bits) (degreeAllowance bits)
  have hn := dimension_le_size bits
  have hd : (degreeAllowance bits).size ≤ CompactSource.size bits :=
    Nat.size_le.mpr Nat.lt_two_pow_self
  have hs := CoercivePowerReaders.size_eq bits
  unfold width CoercivePowerReaders.width
  omega

noncomputable def target (input rank : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthQuery.repack (fun c => dimension (input c) + 1) (width ∘ input)
    (fun c => dimension (input c) + 1) (CoercivePowerReaders.width ∘ input) rank

theorem target_FP {input rank : List Bool → List Bool} (hi : input ∈ FP) (hr : rank ∈ FP) :
    target input rank ∈ FP :=
  FixedWidthQuery.repack_mem_FP ((dimension_unary.comp hi).add (UnaryFn.const 1)) (width_unary.comp hi)
    ((dimension_unary.comp hi).add (UnaryFn.const 1)) (CoercivePowerReaders.width_unary.comp hi) hr

theorem exponent_eq (input rank : List Bool → List Bool) (c : List Bool) :
    CoerciveQueryReaders.queryExponent input (target input rank) c =
      FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (dimension (input c) + 1)))
        (width (input c)) (Nat.fromBitsLE (rank c)) := by
  rw [CoerciveQueryReaders.queryExponent_rank]
  exact FixedWidthPolynomial.nativeExponent_repack
    (Equiv.refl (Fin (dimension (input c) + 1))) (width ∘ input)
    (CoercivePowerReaders.width ∘ input) rank c (width_le (input c))

end LeanCanny.ETR.CoerciveHomogeneousRepack
