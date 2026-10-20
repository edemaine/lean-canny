/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeIndexedSource
public import LeanCanny.ETR.TubeCoefficientBounds

/-! # Degree and coefficient bounds for indexed tube substitution

The next power of two above the actual degree allowance is even, fits every
ranked exponent, and is at most twice that allowance. Its binary writer is FP.
The original tube/projection mass bounds apply uniformly to all ranked terms.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeIndexed
open Complexity
open LeanCanny.Encoding
open Geometry TubeEncoding

theorem blockWidth_pos (bits : List Bool) : 0 < blockWidth bits := by
  have h := degreeBound_lt bits
  have hd : 4 ≤ degreeBound bits := by unfold degreeBound; omega
  by_contra hw
  have he : blockWidth bits = 0 := by omega
  rw [he, pow_zero] at h
  omega

theorem clearingHalf_le (bits : List Bool) : 2 ^ (blockWidth bits - 1) ≤ degreeBound bits := by
  have hw := blockWidth_pos bits
  by_contra h
  have hs := Nat.size_le.mpr (show degreeBound bits < 2 ^ (blockWidth bits - 1) by omega)
  change blockWidth bits ≤ blockWidth bits - 1 at hs
  omega

theorem clearingWidth_eq (bits : List Bool) : 2 ^ blockWidth bits = 2 * 2 ^ (blockWidth bits - 1) := by
  have hw := blockWidth_pos bits
  calc
    _ = 2 ^ ((blockWidth bits - 1) + 1) := congrArg (fun k : ℕ => 2 ^ k) (by omega)
    _ = _ := by rw [pow_succ]; omega

theorem clearingWidth_le (bits : List Bool) : 2 ^ blockWidth bits ≤ 2 * degreeBound bits := by
  rw [clearingWidth_eq]
  exact Nat.mul_le_mul_left 2 (clearingHalf_le bits)

def clearingWidthCode : List Bool → List Bool := Algebra.FixedWidthPolynomial.countCode (fun _ => 1) blockWidth

theorem clearingWidthCode_mem_FP : clearingWidthCode ∈ FP :=
  Algebra.FixedWidthPolynomial.countCode_mem_FP (UnaryFn.const 1) blockWidth_unary

theorem clearingWidthCode_code (bits : List Bool) : clearingWidthCode bits = BinaryNatCode.encode (2 ^ blockWidth bits) := by
  rw [clearingWidthCode, Algebra.FixedWidthPolynomial.countCode_code, Algebra.FixedWidthPolynomial.count, pow_one]

theorem entry_le_clearingWidth (bits : List Bool) (r i : ℕ) :
    Algebra.FixedWidthPolynomial.entry (blockWidth bits) r i ≤ Nat.fromBitsLE (clearingWidthCode bits) := by
  rw [clearingWidthCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact (Algebra.FixedWidthPolynomial.entry_lt _ _ _).le

theorem tubeCoefficient_mass (bits : List Bool) (s : Finset (Constraint (arity bits))) (r : ℕ) :
    (tubeCoefficient bits s r).natAbs ≤ 2 ^ TubeSource.massBudget (CompactSource.size bits) :=
  (Algebra.MvMass.coeff_le _ _).trans (TubeSource.integer_polynomial_mass_le bits s)

theorem projectionCoefficient_mass (bits : List Bool) (s : Finset (Constraint (arity bits)))
    (j : TubeSource.ProjectionIndex bits) (r : ℕ) :
    (projectionCoefficient bits s j r).natAbs ≤ 2 ^ TubeSource.massBudget (CompactSource.size bits) :=
  (Algebra.MvMass.coeff_le _ _).trans (TubeSource.integer_projection_mass_le bits s j)

end LeanCanny.ETR.TubeIndexed
