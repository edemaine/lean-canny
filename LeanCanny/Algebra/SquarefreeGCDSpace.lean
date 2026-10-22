/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SquarefreePartDegreeSpace
public import LeanCanny.Algebra.PolynomialGCDCoefficientSpace

/-! # Derivative-GCD coefficient readers from the original integer polynomial

The computed degree is used inside the prepared determinant query. Constant
inputs produce the empty-minor representative one; no positive-degree
precondition is needed by the coefficient machine.
-/

@[expose] public section

namespace LeanCanny.Algebra.SeparableBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation

theorem derivative_gcd_degree_le (p : ℤ[X]) :
    PolynomialGCDBits.degree p p.derivative ≤ min p.natDegree (p.natDegree - 1) := by
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  by_cases hz : p.natDegree = 0
  · have hd : p.derivative = 0 := derivative_eq_zero.mpr hz
    simp only [PolynomialGCDBits.degree, hd, Polynomial.map_zero, EuclideanDomain.gcd_zero_right,
      natDegree_map_eq_of_injective hi, hz, Nat.zero_sub, Nat.min_self, le_refl]
  · have hq : p.derivative.map (Int.castRingHom ℚ) ≠ 0 :=
      (Polynomial.map_ne_zero_iff hi).mpr (derivative_ne_zero.mpr hz)
    have h := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right (p.map (Int.castRingHom ℚ))
      (p.derivative.map (Int.castRingHom ℚ))) hq
    have hn : PolynomialGCDBits.degree p p.derivative ≤ p.natDegree - 1 := by
      simpa only [PolynomialGCDBits.degree, natDegree_map_eq_of_injective hi, natDegree_derivative] using h
    exact Nat.le_min.mpr ⟨hn.trans (Nat.sub_le _ _), hn⟩

theorem gcdRepresentativeEvaluator (F : Family) (A : Readers F) :
    SpaceFunction (PolynomialGCDBits.value (resultantFamily F)) := by
  have EL : SpaceFunction (access F A).bits.leftCoefficient := by
    simpa only [access] using A.evaluator
  have ER : SpaceFunction (access F A).bits.rightCoefficient := by
    simpa only [access] using DerivativeBits.evaluator A.evaluator modulus modulus_FP
  have D : SpaceFunction (fun c => BinaryNatCode.encode
      (PolynomialGCDBits.degree (F.polynomial c) (F.polynomial c).derivative)) :=
    (gcdDegreeEvaluator F A).congr (funext fun c => by
    simp only [PolynomialGCDBits.degree, SquarefreePart.common, derivative_map])
  have E := PolynomialGCDBits.withOrderEvaluator (access F A) (access_controls F A) EL ER
    (fun c => PolynomialGCDBits.degree (F.polynomial c) (F.polynomial c).derivative) D
    (fun c => derivative_gcd_degree_le (F.polynomial c))
  refine E.congr (funext fun q => ?_)
  simp only [PolynomialGCDBits.orderValue, PolynomialGCDBits.value, PolynomialGCDBits.representative,
    resultantFamily, natDegree_derivative]

end LeanCanny.Algebra.SeparableBits
