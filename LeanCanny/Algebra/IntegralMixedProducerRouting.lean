/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullOldHeightReplies
public import LeanCanny.Algebra.IntegralMixedProducerActualCases
/-! # Chronological leading queries restore their literal creating context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedProducerActualBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedOldBankCofactorBits IntegralMixedFullOldHeightBits
set_option backward.isDefEq.respectTransparency false

theorem leading_query_context (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (z : List Bool) (hb : producerBirth z ≤ birthCap P (RankedHistoryTask.root (pairFst z))) :
    get P .slot15 (writer P (IntegralMixedFullHistoryFamilyBits.routing P D) z) =
      (IntegralMixedFullHistoryFamilyBits.creatingCommand P D
        (IntegralMixedVirtualTaskBits.saved P (writer P (IntegralMixedFullHistoryFamilyBits.routing P D) z))).context := by
  rw [writer, IntegralMixedRoutineContextQuery.query_context P pairFst producerBirth .companion .originalCoefficient]
  · change (IntegralMixedFullHistoryFamilyBits.creatingCommand P D (IntegralMixedFullHistoryFamilyBits.producerKey z)).context = _
    rw [creating_context_snapshot, creating_context_snapshot,
      IntegralMixedFullHistoryFamilyBits.saved_root, IntegralMixedFullHistoryFamilyBits.saved_prefix,
      IntegralMixedRoutineContextQuery.query_root,
      IntegralMixedRoutineContextQuery.query_birth P pairFst producerBirth .companion .originalCoefficient _ _ z hb]
    simp only [IntegralMixedFullHistoryFamilyBits.producerKey, IntegralMixedFullHistoryFamilyBits.prefixLength,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    unfold birthCap at hb
    rw [min_eq_left hb]
  · exact IntegralMixedFullHistoryFamilyBits.routing_context_bound P D z

end LeanCanny.Algebra.IntegralMixedProducerActualBits
