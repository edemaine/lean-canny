/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNativeRelativeFactor
public import LeanCanny.Algebra.IntegralMixedNativeCoefficientSelection
public import LeanCanny.Algebra.IntegralMixedVirtualLayeredCanonical
/-! # Canonical residue witnesses for the actual virtual upper arithmetic -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualCanonicalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualUpperBits
set_option backward.isDefEq.respectTransparency false

private theorem change_modulus {m n : ℕ} {w : List Bool} (h : m = n)
    (hc : ∃ z : ZMod m, residueBits z = w) : ∃ z : ZMod n, residueBits z = w := by
  subst n
  exact hc

theorem reductionEntry_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualMatrixBits.reductionEntry P F q := ⟨_, rfl⟩

theorem reductionPower_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = powerValue P F q := by
  have H : ∃ z : ZMod ((IntegralReductionActionBits.powerFamily (reduction P F)).modulus
      (IntegralCriticalFlatActionBits.packet P (reduction P F) q)), residueBits z = powerValue P F q := by
    unfold powerValue IntegralBlockPowerBits.Family.value
    exact ⟨_, rfl⟩
  have HM : (IntegralReductionActionBits.powerFamily (reduction P F)).modulus
      (IntegralCriticalFlatActionBits.packet P (reduction P F) q) = modulus P q := by
    change (reduction P F).modulus (IntegralBerkowitzBlockBits.original
      (IntegralCriticalFlatActionBits.packet P (reduction P F) q)) = _
    unfold IntegralCriticalFlatActionBits.packet
    rw [IntegralCriticalFlatRelativeFactorBits.outer_original]
    rfl
  exact change_modulus HM H

theorem action_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualMatrixBits.actionEntry P F q := ⟨_, rfl⟩

theorem momentEntry_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = momentEntry P F q := ⟨_, rfl⟩

theorem momentPower_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = momentValue P F q := by
  have H : ∃ z : ZMod ((IntegralBerkowitzBlockBits.momentFamily (characteristic P F)).modulus
      (IntegralCriticalFlatMomentBits.packet P q)), residueBits z = momentValue P F q := by
    unfold momentValue IntegralBlockMomentBits.Family.value
    exact ⟨_, rfl⟩
  have HM : (IntegralBerkowitzBlockBits.momentFamily (characteristic P F)).modulus
      (IntegralCriticalFlatMomentBits.packet P q) = modulus P q := by
    change (characteristic P F).modulus (IntegralBerkowitzBlockBits.original (IntegralCriticalFlatMomentBits.packet P q)) = _
    rw [IntegralCriticalFlatMomentBits.packet_parent, characteristic_task_modulus]
  exact change_modulus HM H

theorem relativeFactor_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualMatrixBits.relativeFactor P F q := ⟨_, rfl⟩

theorem relativePower_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (characteristic P F).value q := by
  have H : ∃ z : ZMod ((characteristic P F).modulus q), residueBits z = (characteristic P F).value q := by
    unfold IntegralBerkowitzBlockBits.Source.value
    exact ⟨_, rfl⟩
  exact change_modulus (characteristic_task_modulus P F q) H

theorem critical_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (critical P F).value q := by
  unfold IntegralClearedCriticalBits.Source.value
  exact ⟨_, rfl⟩

end LeanCanny.Algebra.IntegralMixedVirtualCanonicalBits
