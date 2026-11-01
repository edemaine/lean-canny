/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedProducerRouting
/-! # Current producer values close the actual retained-height recursion -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedProducerActualBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Matches (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (answer : List Bool → List Bool) : Prop where
  leading : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 6 →
    get P .slot15 q ≤ 4 → phase q = 0 → answer q = leading P D q
  companion : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 6 →
    get P .slot15 q ≤ 4 → phase q = 26 → answer q = companion P D q

theorem old_height_replies (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (answer : List Bool → List Bool) (hm : Matches P D answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralMixedFullOldHeightBits.ProducerRepliesAt P D (IntegralMixedFullHistoryFamilyBits.routing P D) answer q := by
  let R := IntegralMixedFullHistoryFamilyBits.routing P D
  let F := IntegralMixedOldHeightBits.bankFamily P D
  let g := IntegralMixedFullHistoryFamilyBits.geometry P D
  constructor
  · intro _ i
    let z := IntegralMixedOldBankCofactorBits.packet P F q i.val
    let c := IntegralMixedOldBankCofactorBits.writer P R z
    have hi : i.val < IntegralMixedOldBankCofactorBits.count P F q := i.isLt
    have hb : IntegralMixedOldBankCofactorBits.producerBirth z ≤ birthCap P (RankedHistoryTask.root (pairFst z)) := by
      simp only [z, IntegralMixedOldBankCofactorBits.producerBirth, IntegralMixedOldBankCofactorBits.packet,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      have he := IntegralMixedOldBankCofactorBits.count_eq P F g q
      have ht : birth P q ≤ birthCap P (RankedHistoryTask.root q) := min_le_right _ _
      omega
    have hx := leading_query_context P D z hb
    have hc : IntegralMixedVirtualCaps.valid P c := by
      unfold IntegralMixedVirtualCaps.valid
      rw [IntegralMixedOldBankCofactorBits.writer_root, show pairFst z = q from pairFst_pair _ _,
        IntegralMixedOldBankCofactorBits.writer_packet_birth P F g R q i.val i.isLt]
      have he := IntegralMixedOldBankCofactorBits.count_eq P F g q
      unfold IntegralMixedVirtualCaps.valid at hv
      omega
    exact (hm.leading c hc (IntegralMixedOldBankCofactorBits.writer_routine P R z)
      (hx.trans_le (IntegralMixedFullHistoryScript.Command.context_le _))
      (IntegralMixedOldBankCofactorBits.writer_phase P R z)).trans (leading_actual P D c hx)
  · intro hq
    let c := IntegralMixedOldHeightBits.writer P R q
    have hx := IntegralMixedFullOldHeightBits.child_context P D q
    have hc : IntegralMixedVirtualCaps.valid P c := by
      unfold IntegralMixedVirtualCaps.valid
      rw [IntegralMixedOldHeightBits.writer_root, IntegralMixedOldHeightBits.writer_birth]
      have ht := IntegralMixedOldHeightBits.producerBirth_lt P q hq
      exact ht.trans hv
    exact (hm.companion c hc (IntegralMixedOldHeightBits.writer_routine P R q)
      (hx.trans_le (IntegralMixedFullHistoryScript.Command.context_le _))
      (IntegralMixedOldHeightBits.writer_phase P R q)).trans
        (companion_actual P D c hx (IntegralMixedFullOldHeightBits.child_coordinate P D q))

theorem old_height_correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullHistoryFamilyBits.Metadata P D) (answer : List Bool → List Bool) (hm : Matches P D answer) :
    NativeControllerBranch.Correct (IntegralMixedFullOldHeightBits.machine P a D h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply IntegralMixedFullOldHeightBits.correct_of_producers P a D h answer
  intro q hq
  apply old_height_replies P D answer hm q
  exact ((IntegralMixedNativeOldHeightBits.selected_iff P q).mp hq).1

end LeanCanny.Algebra.IntegralMixedProducerActualBits
