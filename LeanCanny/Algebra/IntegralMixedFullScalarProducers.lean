/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullScalarMachines
/-! # Earlier producer replies close full scalar denominator and old-height stages -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem physical_leading_replies (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (answer : List Bool → List Bool) (hp : IntegralMixedProducerActualBits.Matches P D answer)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralMixedPhysicalOldBankBits.RepliesAt P (physicalFamily P D) (IntegralMixedFullHistoryFamilyBits.routing P D) answer q := by
  exact IntegralMixedHeightCurrentBits.leading_replies P D answer hp q hv

theorem denominator_correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (answer : List Bool → List Bool) (hp : IntegralMixedProducerActualBits.Matches P D answer) :
    Correct (denominator P a D h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply IntegralMixedPhysicalNativeDenominatorBits.correct P a (physicalFamily P D) h.physical
      (IntegralMixedFullPhysicalBits.geometry P (IntegralMixedFullHistoryFamilyBits.physicalData P D))
      (IntegralMixedFullHistoryFamilyBits.routing P D) (IntegralMixedFullHistoryFamilyBits.routingAccess P D h.full) h.physicalScales answer
    intro q hq
    exact physical_leading_replies P D answer hp q ((IntegralMixedPhysicalNativeDenominatorBits.selected_iff P q).mp hq).1
  · apply IntegralMixedVirtualContextDenominatorBits.correct P a (virtualFamily P D)
      (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) (IntegralMixedFullHistoryFamilyBits.geometry P D)
      (IntegralMixedFullHistoryFamilyBits.routing P D) (IntegralMixedFullHistoryFamilyBits.routingAccess P D h.full) h.virtualScales answer
    intro q hq
    exact IntegralMixedHeightCurrentBits.leading_replies P D answer hp q ((IntegralMixedVirtualContextDenominatorBits.selected_iff P q).mp hq).1

theorem oldHeight_correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (answer : List Bool → List Bool) (hp : IntegralMixedProducerActualBits.Matches P D answer) :
    Correct (oldHeight P a D h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply withGuard_correct _ _ _ answer _ (IntegralMixedProducerActualBits.old_height_correct P a D h.full answer hp)
  intro q hq
  have H := (selected_iff P .clearedHeight q).mp hq
  exact (IntegralMixedNativeOldHeightBits.selected_iff P q).mpr ⟨H.1, H.2.1, H.2.2.1⟩

theorem leading_correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (answer : List Bool → List Bool) :
    Correct (leading P a D h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedFullScalarLeadingBits.correct P a D h.leading answer
end LeanCanny.Algebra.IntegralMixedFullScalarBits
