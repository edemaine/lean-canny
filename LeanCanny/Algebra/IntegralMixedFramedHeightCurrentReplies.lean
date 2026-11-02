/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeHeightActual
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightCurrent
/-! # Current producer and retained-height matches close native scalar-height requests -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeightCurrentBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedOldHeightBits (bankFamily)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Matches (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (answer : List Bool → List Bool) : Prop where
  height : ∀ q, IntegralMixedFramedNativeOldHeightBits.selected P q = true →
    (1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) → answer q = IntegralMixedFramedOldHeightBits.value P D J q

theorem leading_replies (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (answer : List Bool → List Bool) (hm : IntegralMixedFramedProducerActualBits.Matches P D J answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralMixedOldBankCofactorBits.RepliesAt P (bankFamily P D J) (IntegralMixedFramedHeaderBits.routing P D) answer q := by
  exact IntegralMixedFramedProducerActualBits.bank_replies P D J answer hm q hv

theorem replies (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer) (hm : Matches P D J answer)
    (q : List Bool) (hq : IntegralMixedFramedNativeHeightBits.selected P q = true) :
    IntegralMixedFramedHeightTablePassBits.RepliesAt P D J (IntegralMixedFramedHeaderBits.routing P D) answer q := by
  rcases (IntegralMixedFramedNativeHeightBits.selected_iff P q).mp hq with ⟨HV, _HR, _HP, HX⟩
  refine ⟨leading_replies P D J answer hp q HV, ?_⟩
  intro i _
  have HC := IntegralMixedHeightTableQueryBits.writer_selected P q i HV
  have HE : get P .slot15 (IntegralMixedHeightTableQueryBits.writer P (pair q (BinaryNatCode.encode i))) = get P .slot15 q := by
    rw [IntegralMixedHeightTableQueryBits.writer_get]
    rfl
  exact hm.height _ HC (by rwa [HE])

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (hc : IntegralMixedFramedScalarCellsBits.Primitive P D J)
    (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer) (hm : Matches P D J answer) :
    NativeControllerBranch.Correct (IntegralMixedFramedNativeHeightBits.machine P a D J (IntegralMixedFramedHeaderBits.routing P D)
      (IntegralMixedFramedHeaderBits.routingAccess P a D J T ht hr) hc) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedFramedNativeHeightBits.correct P a D J _ (IntegralMixedFramedHeaderBits.routingAccess P a D J T ht hr) hc answer
    (fun q hq => replies P D J answer hp hm q hq)

end LeanCanny.Algebra.IntegralMixedFramedHeightCurrentBits
