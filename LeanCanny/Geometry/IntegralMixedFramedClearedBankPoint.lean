/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankCoordinate
public import LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
/-! # Cleared coordinate polynomials evaluate on the same joint bank point -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedClearedBankPoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankDenominatorBits (count index state)
open IntegralMixedFramedBankCoordinateBits (polynomial weight)
open scoped Classical

theorem eval (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hi : index q<count P D H q) (z : Fin (count P D H q) → ℝ) :
    (polynomial P D H q).eval₂ (Int.castRingHom ℝ) z=
      (IntegralMixedHistory.commonDenominator (state P D H q) : ℝ)*
        IntegralMixedCanonicalBankPoint.point (state P D H q) z ⟨index q,hi⟩ := by
  rw [polynomial,dite_eq_left hi,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X]
  rw [IntegralMixedFramedBankCoordinateBits.weight_actual P D H q hi]
  rw [IntegralMixedFramedBankProductBits.common_split P D H index q ⟨index q,hi⟩ rfl,Int.cast_mul]
  unfold IntegralMixedCanonicalBankPoint.point
  field_simp [IntegralMixedCanonicalBankPoint.denominator_ne_zero (state P D H q) ⟨index q,hi⟩]
  change (IntegralMixedFramedBankProductBits.integer P D H index q : ℝ)*
    z ⟨index q,hi⟩^UniformIntegralPowerSchedule.weights (IntegralMixedFramedBankCoordinateBits.horizon P q)
      (IntegralMixedFramedBankCoordinateBits.scalarDegree P q) (count P D H q) ⟨index q,hi⟩*
      ((state P D H q).bank.denominator ⟨index q,hi⟩ : ℝ)=
    ((state P D H q).bank.denominator ⟨index q,hi⟩ : ℝ)*(IntegralMixedFramedBankProductBits.integer P D H index q : ℝ)*
      z ⟨index q,hi⟩^UniformIntegralPowerSchedule.weights (IntegralMixedFramedBankCoordinateBits.horizon P q)
        (IntegralMixedFramedBankCoordinateBits.scalarDegree P q) (count P D H q) ⟨index q,hi⟩
  ring

end LeanCanny.Geometry.IntegralMixedFramedClearedBankPoint
