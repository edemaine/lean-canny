/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFramedCriticalGuard
/-! # Padding zeros must match the actual selected physical coordinate -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedCriticalGuard
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCriticalGuardBits
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
  (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool)

theorem zero_scalar_iff (ha : Active P T key stage q) (z : Fin (count P T key q)→ℝ)
    (hz : z ⟨scalar P T key stage q,scalar_lt P D H T hr key stage q ha⟩=0) :
    (polynomial P D H T key stage q).eval₂ (Int.castRingHom ℝ) z=0 ↔
      z ⟨physical P T key stage q,physical_lt P D H T hr key stage q ha⟩=0 := by
  rw [zero_iff_actualPoint P D H T hr key stage q ha z,actualPoint_eq P D H T hr key stage q ha z,hz]
  have HS : scalarPower P key stage q≠0 := Nat.ne_of_gt (UniformIntegralPowerSchedule.birth_pos _ _ _)
  have HP : physicalPower P key stage q≠0 := Nat.ne_of_gt (UniformIntegralPowerSchedule.physical_pos _ _ _)
  rw [zero_pow HS,zero_div,eq_comm,pow_eq_zero_iff HP]

theorem reject_padding_zero (ha : Active P T key stage q) (z : Fin (count P T key q)→ℝ)
    (hs : z ⟨scalar P T key stage q,scalar_lt P D H T hr key stage q ha⟩=0)
    (hp : z ⟨physical P T key stage q,physical_lt P D H T hr key stage q ha⟩≠0) :
    (polynomial P D H T key stage q).eval₂ (Int.castRingHom ℝ) z≠0 :=
  fun h=>hp ((zero_scalar_iff P D H T hr key stage q ha z hs).mp h)
end LeanCanny.Geometry.IntegralMixedFramedCriticalGuard
