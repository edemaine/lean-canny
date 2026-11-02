/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedUnitSnapshot
/-! # Unit snapshots from literal creating-rule syntax -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedUnitSnapshotBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedScalarCellsBits
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem Snapshot.of_rules (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool)
    (hL : ∀ key, (IntegralMixedFramedHistoryFamilyBits.instruction P D key).source.leading = 1)
    (hp : ∀ key, (physicalFamily P D H).rule key =
      IntegralMixedFramedUnitBodyBits.critical P writer true key ((physicalFamily P D H).rule key).offset
        ((physicalFamily P D H).rule key).objective ((physicalFamily P D H).rule key).coordinate)
    (hf : ∀ key, IntegralMixedFramedUnitBodyBits.height P writer key < ((virtualFamily P D H).rule key).critical.offset.val)
    (hv : ∀ key, (virtualFamily P D H).rule key =
      IntegralMixedFramedUnitBodyBits.sweep P writer key ((virtualFamily P D H).rule key).critical.offset
        ((virtualFamily P D H).rule key).critical.objective ((virtualFamily P D H).rule key).critical.coordinate (hf key)) :
    Snapshot P D H writer where
  leading := hL
  physicalScales := by intro key i; rw [hp key]; rfl
  virtualScales := by intro key i; rw [hv key]; rfl
  physicalHeights := by intro key i; rw [hp key]; rfl
  virtualHeights := by intro key i; rw [hv key]; rfl
  height := by intro key; exact congrArg (fun r => (IntegralMixedCriticalSweep.Rule.height r).val) (hv key)
  slope := by intro key; exact congrArg IntegralMixedCriticalSweep.Rule.slope (hv key)
end LeanCanny.Algebra.IntegralMixedFramedUnitSnapshotBits
