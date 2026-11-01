/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeTopPower
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeInverse
/-! # Immutable leading powers and inverse coefficients under phase retargeting -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

noncomputable def topPowerAt (F : Family) (key : List Bool) (m k r t : ℕ) : List Bool :=
  residueBits ((((top F key).map (Int.castRingHom (ZMod m))) ^ k)
    ⟨r % dimension F key, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % dimension F key, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩)

theorem topPower_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    topPowerValue P F q = topPowerAt F (IntegralMixedVirtualTaskBits.saved P q)
      (modulus P q) (get P .target q) (get P .row q) (get P .col q) := rfl

attribute [local irreducible] topPowerAt

theorem topPower_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    topPowerValue P F (IntegralCriticalFlatEulerBits.next P p q) = topPowerValue P F q := by
  rw [topPower_snapshot, topPower_snapshot, saved_next, IntegralCriticalFlatEulerBits.next_modulus,
    IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatEulerBits.next_get]

theorem inverseValue_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    inverseValue P F (IntegralCriticalFlatEulerBits.next P p q) = inverseValue P F q := by
  unfold inverseValue
  rw [saved_next, IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatEulerBits.next_modulus]

theorem next_valid (P : Parameters) (p : Phase) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralMixedVirtualCaps.valid P (IntegralCriticalFlatEulerBits.next P p q) := by
  unfold IntegralMixedVirtualCaps.valid
  rw [IntegralCriticalFlatEulerBits.next_birth, IntegralCriticalFlatEulerBits.next_root]
  exact hv

theorem next_routine (P : Parameters) (p : Phase) (q : List Bool) :
    IntegralMixedRoutineTaskBits.routine P (IntegralCriticalFlatEulerBits.next P p q) = IntegralMixedRoutineTaskBits.routine P q := by
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatEulerBits.next_get]

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
