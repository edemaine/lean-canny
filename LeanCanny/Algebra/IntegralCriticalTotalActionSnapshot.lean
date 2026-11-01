/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingSnapshot
public import LeanCanny.Algebra.IntegralCriticalFlatReductionPower
public import LeanCanny.Algebra.IntegralReductionActionFreeze
/-! # Actual shifted-power values retained by phase-only child writers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalActionSnapshotBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources
set_option backward.isDefEq.respectTransparency false

noncomputable def powerAt (A : IntegralHistoryCriticalBits.Family) (r t : ℕ) : List Bool :=
  IntegralReductionActionFreezeBits.atPower (IntegralCriticalQuerySnapshotBits.canonicalReduction A) r t

noncomputable def powerValue (F : Scripts) (q : List Bool) : List Bool :=
  (IntegralReductionActionBits.powerFamily (reduction F)).value
    (IntegralCriticalFlatActionBits.packet F.toParameters (reduction F) q)

attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily

theorem freeze_snapshot (F : Scripts) (q : List Bool) :
    IntegralReductionActionFreezeBits.freeze (reduction F) q =
      IntegralCriticalQuerySnapshotBits.canonicalReduction (IntegralCriticalTotalSnapshotBits.family F q) := rfl

theorem power_snapshot (F : Scripts) (q : List Bool) : powerValue F q =
    powerAt (IntegralCriticalTotalSnapshotBits.family F q)
      (get F.toParameters .row q) (get F.toParameters .col q) := by
  simp only [powerValue, IntegralCriticalFlatActionBits.packet, IntegralBerkowitzBlockBits.outerPacket,
    IntegralCriticalFlatRelativeFactorBits.packet, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have H := IntegralReductionActionFreezeBits.value_freeze (reduction F) q
    (get F.toParameters .row q) (get F.toParameters .col q)
  simp only [BinaryNatCode.encode] at H
  rw [H, freeze_snapshot]
  rfl

attribute [local irreducible] powerAt

theorem power_next (F : Scripts) (p : Phase) (q : List Bool) :
    powerValue F (IntegralCriticalFlatEulerBits.next F.toParameters p q) = powerValue F q := by
  rw [power_snapshot, power_snapshot, IntegralCriticalTotalSnapshotBits.family_next,
    IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatEulerBits.next_get]

end LeanCanny.Algebra.IntegralCriticalTotalActionSnapshotBits
