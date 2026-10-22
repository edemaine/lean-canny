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
  let A : List Bool → ℕ := fun c => dimension (input c) + 1
  let W := width ∘ input
  let V := CoercivePowerReaders.width ∘ input
  have hfit (i : ℕ) : FixedWidthQuery.entry A W rank c i < 2 ^ V c := by
    unfold FixedWidthQuery.entry
    split_ifs
    · apply (Nat.fromBitsLE_lt_pow_length _).trans_le
      apply Nat.pow_le_pow_right (by decide)
      exact (List.length_take_le _ _).trans (width_le (input c))
    · exact Nat.two_pow_pos _
  ext i
  simp only [CoerciveQueryReaders.queryExponent, FixedWidthPolynomial.nativeExponent,
    Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply]
  change FixedWidthQuery.coordinate V (FixedWidthQuery.repack A W A V rank) c i.val = _
  rw [FixedWidthQuery.coordinate_repack A W A V rank c i.val i.isLt (hfit i.val)]
  rw [FixedWidthQuery.entry, ite_eq_left i.isLt]
  unfold FixedWidthQuery.coordinate
  rw [FixedWidthPolynomial.entry_eq_digit, BinaryNat.value_take, FixedWidthPolynomial.drop_value]
  rfl

end LeanCanny.ETR.CoerciveHomogeneousRepack
