/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialGCDDegreeSpace
public import LeanCanny.Algebra.SeparableSpace
public import LeanCanny.Algebra.SquarefreePart

/-! # Native degree controls for square-free preprocessing

The original coefficient reader supplies its own derivative through modular
multiplication. The principal-minor scan computes the derivative GCD degree;
subtraction gives the square-free quotient degree. Constant and zero inputs
are handled without a positive-degree assumption on the source family.
-/

@[expose] public section

namespace LeanCanny.Algebra.SeparableBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
attribute [local irreducible] BinaryNat.sub

theorem gcdDegreeEvaluator (F : Family) (A : Readers F) :
    SpaceFunction (fun c => BinaryNatCode.encode
      (SquarefreePart.common ((F.polynomial c).map (Int.castRingHom ℚ))).natDegree) := by
  have EL : SpaceFunction (access F A).bits.leftCoefficient := by
    simpa only [access] using A.evaluator
  have ER : SpaceFunction (access F A).bits.rightCoefficient := by
    simpa only [access] using DerivativeBits.evaluator A.evaluator modulus modulus_FP
  have E := PolynomialGCDBits.scanDegreeEvaluator (access F A) (access_controls F A) EL ER
  refine E.congr (funext fun c => congrArg BinaryNatCode.encode ?_)
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  by_cases hz : (F.polynomial c).natDegree = 0
  · have hd : (F.polynomial c).derivative = 0 := derivative_eq_zero.mpr hz
    simp only [PolynomialGCDBits.scanDegree, resultantFamily, hz, Nat.zero_sub,
      SquarefreePart.common, derivative_map, hd, Polynomial.map_zero, EuclideanDomain.gcd_zero_right,
      natDegree_map_eq_of_injective hi]
  · have h := PolynomialGCDBits.scanDegree_eq (access F A) c rfl
      (natDegree_derivative _).symm (derivative_ne_zero.mpr hz) (natDegree_derivative_lt hz)
    simpa only [PolynomialGCDBits.degree, resultantFamily, SquarefreePart.common, derivative_map] using h

def quotientDegreeFinish {F : Family} (A : Readers F) (z : List Bool) : List Bool :=
  BinaryNat.sub (pair (A.degree (pairFst z)) (pairSnd z))

theorem quotientDegreeFinish_FP {F : Family} (A : Readers F) : quotientDegreeFinish A ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP A.degreeFP) pairSnd_mem_FP) BinaryNat.sub_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem squarefreeDegreeEvaluator (F : Family) (A : Readers F) (hne : ∀ c, F.polynomial c ≠ 0) :
    SpaceFunction (fun c => BinaryNatCode.encode
      (SquarefreePart.part ((F.polynomial c).map (Int.castRingHom ℚ))).natDegree) := by
  have R := (gcdDegreeEvaluator F A).withInput.postcompose (quotientDegreeFinish A) (quotientDegreeFinish_FP A)
  refine R.congr (funext fun c => ?_)
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  simp only [Function.comp_apply, quotientDegreeFinish, pairFst_pair, pairSnd_pair, A.degree_eq,
    BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [SquarefreePart.part_natDegree _ ((Polynomial.map_ne_zero_iff hi).mpr (hne c)),
    natDegree_map_eq_of_injective hi]

end LeanCanny.Algebra.SeparableBits
