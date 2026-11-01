/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueRowDispatcher

/-! # Internal value-row replies follow from the actual routine-two model

No matrix evaluator is assumed here. The single model invariant used by
the ranked global controller resolves each current internal child through
its literal emitted phase and unchanged valid producer prefix.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueRowInternalReplies
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualCaps IntegralMixedValueRowModel
open scoped Classical

theorem valid_transport (P : Parameters) (q c : List Bool) (hv : valid P q)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q) : valid P c := by
  unfold valid
  rw [hr, hb]
  exact hv

theorem at_phase (P : Parameters) (F : Family) (answer : List Bool → List Bool) (h : Matches P F answer)
    (q : List Bool) (p : ℕ) (hlo : 21 ≤ p) (hhi : p ≤ 26) (hv : valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) (hp : phase q = p) :
    answer q = component P F p q := by
  have HE := h q hv hr (by omega) (by omega)
  rw [hp] at HE
  exact HE

theorem homogeneous_original (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (h : Matches P F answer) (q : List Bool) (hv : valid P q) :
    answer (IntegralMixedValueHomogeneousQueries.originalTask P F q) =
      IntegralMixedValueRestoredSource.value P F (IntegralMixedValueHomogeneousQueries.originalTask P F q) := by
  apply at_phase P F answer h _ 21 (by decide) (by decide)
  · apply valid_transport P q _ hv
    · exact IntegralMixedValueFieldQuery.query_root P id .pscEntry .momentEntry .target (IntegralMixedValueHomogeneousQueries.originalTarget P F) q
    · exact IntegralMixedValueFieldQuery.query_birth P id .pscEntry .momentEntry .target (IntegralMixedValueHomogeneousQueries.originalTarget P F) q
  · exact IntegralMixedValueFieldQuery.query_routine P id .pscEntry .momentEntry .target (IntegralMixedValueHomogeneousQueries.originalTarget P F) q
  · exact IntegralMixedValueFieldQuery.query_phase P id .pscEntry .momentEntry .target (IntegralMixedValueHomogeneousQueries.originalTarget P F) q

theorem reciprocal (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (h : Matches P F answer) (q : List Bool) (hv : valid P q) :
    IntegralMixedValueReciprocalRequest.RepliesAt P F answer q := by
  intro _
  apply at_phase P F answer h _ 22 (by decide) (by decide)
  · exact valid_transport P q _ hv (IntegralMixedValueReciprocalTasks.query_root P F q)
      (IntegralMixedValueReciprocalTasks.query_birth P F q)
  · exact IntegralMixedValueFieldQuery.query_routine P (IntegralMixedValueReciprocalTasks.rowTask P F) .pscEntry .momentPower .col (IntegralMixedValueReciprocalTasks.oldCol P F) q
  · exact IntegralMixedValueFieldQuery.query_phase P (IntegralMixedValueReciprocalTasks.rowTask P F) .pscEntry .momentPower .col (IntegralMixedValueReciprocalTasks.oldCol P F) q

theorem macaulay (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (h : Matches P F answer) (q : List Bool) (hv : valid P q) :
    IntegralMixedValueMacaulayRequest.RepliesAt P F answer q := by
  intro _
  apply at_phase P F answer h _ 23 (by decide) (by decide)
  · exact valid_transport P q _ hv (IntegralMixedValueMacaulayTasks.query_root P F q)
      (IntegralMixedValueMacaulayTasks.query_birth P F q)
  · exact IntegralMixedValueFieldQuery.query_routine P (IntegralMixedValueMacaulayTasks.sourceTask P F) .pscEntry .relativeFactor .target (IntegralMixedValueMacaulayTasks.difference P F) q
  · exact IntegralMixedValueFieldQuery.query_phase P (IntegralMixedValueMacaulayTasks.sourceTask P F) .pscEntry .relativeFactor .target (IntegralMixedValueMacaulayTasks.difference P F) q

theorem product (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (h : Matches P F answer) (q : List Bool) (hv : valid P q) :
    IntegralMixedValueGramProductNative.RepliesAt P F answer q := by
  intro left
  apply at_phase P F answer h _ 24 (by decide) (by decide)
  · exact valid_transport P q _ hv (IntegralMixedValueGramProductTasks.query_root P F left q)
      (IntegralMixedValueGramProductTasks.query_birth P F left q)
  · exact IntegralMixedValueFieldQuery.query_routine P (IntegralMixedValueGramProductTasks.third P F left) .pscEntry .relativePower .col (IntegralMixedValueGramProductTasks.col P F left) q
  · exact IntegralMixedValueFieldQuery.query_phase P (IntegralMixedValueGramProductTasks.third P F left) .pscEntry .relativePower .col (IntegralMixedValueGramProductTasks.col P F left) q

theorem sum (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (h : Matches P F answer) (q : List Bool) (hv : valid P q) :
    IntegralMixedValueGramSumChildren.RepliesAt P F answer q := by
  intro k _
  apply at_phase P F answer h _ 25 (by decide) (by decide)
  · apply valid_transport P q _ hv
    · simpa only [IntegralMixedValueGramSumTasks.query, pairFst_pair] using IntegralMixedValueFieldQuery.query_root P pairFst .pscEntry
        .criticalCoefficient .slot10 (fun z => Nat.fromBitsLE (pairSnd z)) (pair q (BinaryNatCode.encode k))
    · simpa only [IntegralMixedValueGramSumTasks.query, pairFst_pair] using IntegralMixedValueFieldQuery.query_birth P pairFst .pscEntry
        .criticalCoefficient .slot10 (fun z => Nat.fromBitsLE (pairSnd z)) (pair q (BinaryNatCode.encode k))
  · exact IntegralMixedValueFieldQuery.query_routine P pairFst .pscEntry .criticalCoefficient .slot10
      (fun z => Nat.fromBitsLE (pairSnd z)) (pair q (BinaryNatCode.encode k))
  · exact IntegralMixedValueFieldQuery.query_phase P pairFst .pscEntry .criticalCoefficient .slot10
      (fun z => Nat.fromBitsLE (pairSnd z)) (pair q (BinaryNatCode.encode k))

end LeanCanny.Algebra.IntegralMixedValueRowInternalReplies
