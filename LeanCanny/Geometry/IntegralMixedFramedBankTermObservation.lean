/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFramedBankTermSign
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # Term coordinates agree with the bank-only observation -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedBankTermSign
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open IntegralMixedFramedBankTermBits (reverseIndex reverse_lt)

theorem point_observation (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (z : ℕ→ℝ) (i : ℕ) (hi : i<(atKey P D H key).count) :
    point P D H key (fun j=>z j.val) i=
      (IntegralMixedFramedBankObservation.ofState (state P D H key)).point z (reverseIndex P D H key i) := by
  unfold point IntegralMixedFramedBankObservation.Data.point
  have HR : reverseIndex P D H key i<
      (IntegralMixedFramedBankObservation.ofState (state P D H key)).count := reverse_lt P D H key i hi
  rw [dite_eq_left hi,dite_eq_left HR]
  rfl

end LeanCanny.Geometry.IntegralMixedFramedBankTermSign
