/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBounds
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # Active source packets are the actual bank-coordinate annihilators -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem matrix_actual (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (ha : Active P c) (hi : index c<count P D H c) :
    matrix P D H c=IntegralMixedBankCoordinatePolynomial.matrix ((family P D H).state (key c)) ⟨index c,hi⟩ := by
  funext r t
  rw [matrix,ite_eq_left ha,min_eq_left hi.le]
  unfold IntegralMixedFramedOldHeightBankBits.sourceEntry
  rw [dite_eq_left ⟨hi,r.isLt,t.isLt⟩]
  rfl

theorem matrix_inactive (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (ha : ¬Active P c) : matrix P D H c=0 := by
  funext r t
  exact ite_eq_right ha

theorem matrix_outside (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (hi : count P D H c ≤ index c) : matrix P D H c=0 := by
  funext r t
  rw [matrix,min_eq_right hi]
  split_ifs with ha
  · unfold IntegralMixedFramedOldHeightBankBits.sourceEntry
    rw [dite_eq_right (fun hv => (Nat.lt_irrefl (count P D H c)) hv.1)]
    rfl
  · rfl

theorem polynomial_actual (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (ha : Active P c) (hi : index c<count P D H c) :
    polynomial P D H c=IntegralMixedBankCoordinatePolynomial.polynomial ((family P D H).state (key c)) ⟨index c,hi⟩ := by
  rw [polynomial,matrix_actual P D H c ha hi]
  rfl

theorem quotient_root (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (ha : Active P c) (hi : index c<count P D H c)
    (φ : ((family P D H).state (key c)).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    (polynomial P D H c).eval₂ (Int.castRingHom ℝ)
      (φ (((family P D H).state (key c)).bank.numerator ⟨index c,hi⟩)/
        ((((family P D H).state (key c)).bank.denominator ⟨index c,hi⟩ : ℝ)))=0 := by
  rw [polynomial_actual P D H c ha hi]
  exact IntegralMixedBankCoordinatePolynomial.quotient_root ((family P D H).state (key c)) φ ⟨index c,hi⟩

theorem point_root (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (ha : Active P c) (hi : index c<count P D H c)
    (z : Fin (count P D H c) → ℝ)
    (hz : ∀ i, (((family P D H).state (key c)).sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    (polynomial P D H c).eval₂ (Int.castRingHom ℝ)
      ((IntegralMixedFramedBankObservation.ofState ((family P D H).state (key c))).point
        (IntegralMixedFramedBankObservation.extend z) (index c))=0 := by
  rw [polynomial_actual P D H c ha hi,
    IntegralMixedFramedBankObservation.point_ofState ((family P D H).state (key c)) z ⟨index c,hi⟩]
  exact IntegralMixedBankCoordinatePolynomial.point_root ((family P D H).state (key c))
    (IntegralMixedFramedHistoryFamilyBits.family_canonical P D H (key c)) z hz ⟨index c,hi⟩

end LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
