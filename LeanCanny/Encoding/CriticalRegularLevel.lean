/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FermatRegularSource
public import LeanCanny.Algebra.FixedWidthPolynomialFP
public import LeanCanny.Algebra.DyadicConstantCoefficient
public import LeanCanny.Geometry.IntegerRegularSource
public import LeanCanny.Algebra.FixedWidthDyadicScaleSpace

/-! # Native binary metadata for the constructed regular level

Unary dimension and binary source degree and mass exponent suffice to compute
the selected level exponent in polynomial time. Modular access to the dyadic
denominator uses that exponent directly.
-/

@[expose] public section
namespace LeanCanny.Encoding.CriticalRegularLevel
open LeanCanny.Algebra
open Geometry

theorem width_unary {dim degree : List Bool → ℕ} (hd : UnaryFn dim) (hN : BinaryFn degree) :
    UnaryFn (fun c => FermatRegularSource.width (dim c) (degree c)) := by
  have hval := (((hN.sub (BinaryFn.const 1)).add
    (((BinaryFn.ofUnary hd).add (BinaryFn.const 1)).mul
      ((hN.sub (BinaryFn.const 1)).sub (BinaryFn.const 1)))).add (BinaryFn.const 1))
  have hs := UnaryFn.length hval.bits_mem_FP
  exact hs.of_eq (fun c => by rw [BinaryNatCode.length_encode, FermatRegularSource.width_eq])

theorem exponent_binary {dim degree mass : List Bool → ℕ}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hb : BinaryFn mass) :
    BinaryFn (fun c => Geometry.CriticalRegularLevel.exponent (dim c + 1) (degree c)
      (FermatRegularSource.width (dim c) (degree c)) (mass c)) := by
  have hC := BinaryFn.of_bits (mem_FP_of_eq
    (FixedWidthPolynomial.countCode_mem_FP (hd.add (UnaryFn.const 3)) (width_unary hd hN))
    (fun c => FixedWidthPolynomial.countCode_code _ _ c))
  have hcoeff := ((hC.size.mul hC).add
    (hC.mul (((hb.add hN.size).add (BinaryFn.const 1)).add (BinaryFn.const 3)))).add (BinaryFn.const 1)
  have hm := hcoeff.add ((hC.add (BinaryFn.const 1)).size)
  exact (hm.add (BinaryFn.const 1)).of_eq (fun _ => rfl)

theorem denominator_coefficient_FP {dim degree mass : List Bool → ℕ}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hb : BinaryFn mass) :
    PrimitivePairBits.coefficient (fun c => Polynomial.C
      ((2 ^ Geometry.CriticalRegularLevel.exponent (dim c + 1) (degree c)
        (FermatRegularSource.width (dim c) (degree c)) (mass c) : ℕ) : ℤ)) ∈ FP :=
  DyadicConstantBits.coefficient_FP (exponent_binary hd hN hb)

/-- A native coefficient evaluator for the original integer polynomial
supplies one for its constructed regular integer source. -/
theorem integerSource_evaluator {dim degree mass A W : List Bool → ℕ}
    {target modulus coefficient : List Bool → List Bool}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hb : BinaryFn mass)
    (hA : UnaryFn A) (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (P : Computation.SpaceFunction coefficient) :
    Computation.SpaceFunction (FixedWidthDyadicScaleBits.value A W
      (fun c => IntegerRegularSource.exponent (dim c) (degree c) (mass c)) target modulus coefficient) :=
  FixedWidthDyadicScaleBits.evaluator A W _ target modulus P hA hW (exponent_binary hd hN hb) ht hm

end LeanCanny.Encoding.CriticalRegularLevel
