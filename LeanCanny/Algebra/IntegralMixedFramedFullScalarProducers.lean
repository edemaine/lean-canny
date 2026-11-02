/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarMachines
/-! # Earlier producer replies close full scalar denominator and old-height stages -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem physical_leading_replies (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralMixedPhysicalOldBankBits.RepliesAt P (physicalFamily P D J) (IntegralMixedFramedHeaderBits.routing P D) answer q := by
  exact IntegralMixedFramedHeightCurrentBits.leading_replies P D J answer hp q hv

theorem denominator_correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer) :
    Correct (denominator P a D J h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply IntegralMixedPhysicalNativeDenominatorBits.correct P a (physicalFamily P D J) (physicalInput P a D J h)
      (IntegralMixedFramedPhysicalBits.geometry P D J)
      (IntegralMixedFramedHeaderBits.routing P D) (routingAccess P a D J h) h.physicalScales answer
    intro q hq
    exact physical_leading_replies P D J answer hp q ((IntegralMixedPhysicalNativeDenominatorBits.selected_iff P q).mp hq).1
  · apply IntegralMixedVirtualContextDenominatorBits.correct P a (virtualFamily P D J)
      (virtualInput P a D J h) (IntegralMixedFramedHistoryFamilyBits.geometry P D J)
      (IntegralMixedFramedHeaderBits.routing P D) (routingAccess P a D J h) h.virtualScales answer
    intro q hq
    exact IntegralMixedFramedHeightCurrentBits.leading_replies P D J answer hp q ((IntegralMixedVirtualContextDenominatorBits.selected_iff P q).mp hq).1

theorem oldHeight_correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer) :
    Correct (oldHeight P a D J h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply withGuard_correct _ _ _ answer _ (IntegralMixedFramedOldHeightBits.correct_of_matches P a D J h.tables h.native h.represents answer hp)
  intro q hq
  have H := (selected_iff P .clearedHeight q).mp hq
  exact (IntegralMixedFramedNativeOldHeightBits.selected_iff P q).mpr ⟨H.1, H.2.1, H.2.2.1⟩

theorem leading_correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D J) (answer : List Bool → List Bool) :
    Correct (leading P a D J h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedFramedScalarLeadingBits.correct P a D J h.leading answer
end LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
