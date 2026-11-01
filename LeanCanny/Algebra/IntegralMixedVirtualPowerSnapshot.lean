/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNativeReductionPower
/-! # Virtual reduction powers under phase-only child retargeting -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

noncomputable def powerAt (A : IntegralClearedCriticalBits.Source) (r t : ℕ) : List Bool :=
  IntegralReductionActionFreezeBits.atPower
    (IntegralPurePowerActionBits.reductionSource (IntegralClearedCriticalBits.relativeSource A)) r t

theorem power_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    powerValue P F q = powerAt (IntegralMixedVirtualSnapshotBits.family P F q) (get P .row q) (get P .col q) := by
  simp only [powerValue, IntegralCriticalFlatActionBits.packet, IntegralBerkowitzBlockBits.outerPacket,
    IntegralCriticalFlatRelativeFactorBits.packet, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have H := IntegralReductionActionFreezeBits.value_freeze (reduction P F) q (get P .row q) (get P .col q)
  simp only [BinaryNatCode.encode] at H
  rw [H, freeze_reduction]
  rfl

attribute [local irreducible] powerAt

theorem power_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    powerValue P F (IntegralCriticalFlatEulerBits.next P p q) = powerValue P F q := by
  rw [power_snapshot, power_snapshot, IntegralMixedVirtualSnapshotBits.family_next,
    IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatEulerBits.next_get]

end LeanCanny.Algebra.IntegralMixedVirtualUpperBits
