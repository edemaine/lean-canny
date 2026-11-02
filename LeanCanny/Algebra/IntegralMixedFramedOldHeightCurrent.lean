/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightRouting
public import LeanCanny.Algebra.IntegralMixedFramedBankProducerReplies
/-! # Current framed producer values close every retained-height request -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedOldHeightBits (request writer)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem current_replies (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (answer : List Bool → List Bool) (own : IntegralMixedFramedProducerActualBits.Matches P D H answer)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    PassRepliesAt P D H (IntegralMixedFramedHeaderBits.routing P D) answer q := by
  constructor
  · intro _
    exact IntegralMixedFramedProducerActualBits.bank_replies P D H answer own q hv
  · intro hq
    let R := IntegralMixedFramedHeaderBits.routing P D
    let c := writer P R q
    have hx := child_context P D q
    have hc : IntegralMixedVirtualCaps.valid P c := by
      unfold IntegralMixedVirtualCaps.valid
      rw [IntegralMixedOldHeightBits.writer_root, IntegralMixedOldHeightBits.writer_birth]
      exact (IntegralMixedOldHeightBits.producerBirth_lt P q hq).trans hv
    exact (own.companion c hc (IntegralMixedOldHeightBits.writer_routine P R q)
      (hx.trans_le (IntegralMixedFullHistoryScript.Command.context_le _))
      (IntegralMixedOldHeightBits.writer_phase P R q)).trans
        (IntegralMixedFramedProducerActualBits.companion_actual P D H c hx (child_coordinate P D q))

theorem correct_of_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D H T) (answer : List Bool → List Bool)
    (own : IntegralMixedFramedProducerActualBits.Matches P D H answer) :
    NativeControllerBranch.Correct (machine P a D H T ht hr) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply correct P a D H T ht hr answer
  intro q hq
  exact current_replies P D H answer own q ((IntegralMixedFramedNativeOldHeightBits.selected_iff P q).mp hq).1

theorem correct_of_dispatcher_matches (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedProducerBits.Controls P D H) (answer : List Bool → List Bool)
    (own : IntegralMixedFramedProducerBits.Matches P a D H h answer) :
    NativeControllerBranch.Correct (machine P a D H h.tables h.native h.represents) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct_of_matches P a D H h.tables h.native h.represents answer
    (IntegralMixedFramedProducerBits.producer_matches P a D H h answer own)
end LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
