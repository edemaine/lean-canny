/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedProducerValues
/-! # Actual creator labels survive earlier-prefix producer queries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedProducerActualBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction prefixLength)
open IntegralMixedOldBankCofactorBits
open scoped Classical

noncomputable def contextSnapshot (P : Parameters) (D : Plan P) (root : List Bool) (birth : ℕ) : ℕ :=
  ((IntegralMixedFramedHistoryScript.chronological (D.rules root) birth).getD
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)).command.context
noncomputable def coordinateSnapshot (P : Parameters) (D : Plan P) (root : List Bool) (birth : ℕ) : ℕ :=
  ((IntegralMixedFramedHistoryScript.chronological (D.rules root) birth).getD
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)).command.coordinate

theorem instruction_context_snapshot (P : Parameters) (D : Plan P) (key : List Bool) :
    (instruction P D key).command.context=contextSnapshot P D (pairFst key) (prefixLength P key) := rfl

theorem instruction_coordinate_snapshot (P : Parameters) (D : Plan P) (key : List Bool) :
    (instruction P D key).command.coordinate=coordinateSnapshot P D (pairFst key) (prefixLength P key) := rfl

theorem framed_saved_prefix (P : Parameters) (q : List Bool) :
    prefixLength P (IntegralMixedVirtualTaskBits.saved P q)=birth P q :=
  IntegralMixedFullHistoryFamilyBits.saved_prefix P q

theorem leading_query_context (P : Parameters) (D : Plan P) (z : List Bool)
    (hb : producerBirth z≤birthCap P (RankedHistoryTask.root (pairFst z))) :
    get P .slot15 (writer P (IntegralMixedFramedHeaderBits.routing P D) z)=
      (instruction P D (IntegralMixedVirtualTaskBits.saved P (writer P (IntegralMixedFramedHeaderBits.routing P D) z))).command.context := by
  rw [writer,IntegralMixedRoutineContextQuery.query_context P pairFst producerBirth .companion .originalCoefficient]
  · change (instruction P D (IntegralMixedFullHistoryFamilyBits.producerKey z)).command.context=_
    rw [instruction_context_snapshot,instruction_context_snapshot,
      IntegralMixedFullHistoryFamilyBits.saved_root,framed_saved_prefix,
      IntegralMixedRoutineContextQuery.query_root,
      IntegralMixedRoutineContextQuery.query_birth P pairFst producerBirth .companion .originalCoefficient _ _ z hb]
    simp only [IntegralMixedFullHistoryFamilyBits.producerKey,IntegralMixedFullHistoryFamilyBits.prefixLength,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    unfold birthCap at hb
    rw [min_eq_left hb]
  · exact IntegralMixedFramedHeaderBits.routing_context_bound P D z

end LeanCanny.Algebra.IntegralMixedFramedProducerActualBits
