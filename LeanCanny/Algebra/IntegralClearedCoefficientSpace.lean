/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralClearedCoefficientCorrect
public import LeanCanny.Algebra.ModularSumSpace

/-! # Native actual frozen-substitution coefficients from original readers

Stream the original spatial exponent grid, mask the free exponents, and
sum the constructed term multiplication-matrix entries. Only the original
coefficient, integer-denominator, and retained-height readers are supplied;
their full space costs are charged. No parameter-polynomial expansion or
division modulo the caller modulus is used.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralClearedCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Source.value maskedProgram

theorem evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) : SpaceFunction S.value := by
  have E := masked_evaluator S a EC EH EQ
  have HC := FixedWidthPolynomial.countCode_mem_FP a.arity a.sourceWidth
  have HM : (fun c => BinaryNatCode.encode (S.modulus c)) ∈ FP := a.modulus.bits_mem_FP
  have HV : (fun c => Nat.fromBitsLE (BinaryNatCode.encode (S.modulus c))) = S.modulus :=
    funext (fun c => Nat.fromBitsLE_bits _)
  have H := ModularSum.evaluatorWithModulus E (FixedWidthPolynomial.countCode S.arity S.sourceWidth)
    (fun c => BinaryNatCode.encode (S.modulus c)) HC HM S.modulus HV
    (fun c i => (S.summand c i : ZMod (S.modulus c)))
    (fun c => Nat.pos_of_ne_zero (S.modulus_ne_zero c)) (fun c i hi => by
      apply masked_packet S c i
      simpa only [FixedWidthPolynomial.countCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi)
  refine H.congr (funext fun c => ?_)
  rw [FixedWidthPolynomial.countCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact sum_value S c

end LeanCanny.Algebra.IntegralClearedCoefficientBits
