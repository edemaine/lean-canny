/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueRowCorrect
public import LeanCanny.Computation.NativeRequestInvariant
/-! # Value-row query contexts are literal fields of the saved source key -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueRowContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

def ContextEq (P : Parameters) (q c : List Bool) : Prop := get P .slot15 c = get P .slot15 q

theorem context_of_saved (P : Parameters) (q c : List Bool)
    (hs : IntegralMixedVirtualTaskBits.saved P c = IntegralMixedVirtualTaskBits.saved P q) : ContextEq P q c := by
  have HE := congrArg (fun z => Nat.fromBitsLE (pairSnd (pairSnd z))) hs
  simpa only [ContextEq, IntegralMixedVirtualTaskBits.saved, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using HE

theorem low_context (P : Parameters) (F : Family) (q : List Bool) : ContextEq P q (IntegralMixedFullRowTasks.lowTask P F q) := by
  unfold IntegralMixedFullRowTasks.lowTask
  split_ifs <;> exact context_of_saved P q _ (IntegralMixedFullRowTasks.task_saved P F _ _ q)

theorem scalar_context (P : Parameters) (F : Family) (q : List Bool) : ContextEq P q (IntegralMixedFullRowTasks.scalarTask P F q) := by
  unfold IntegralMixedFullRowTasks.scalarTask IntegralMixedOriginalScaleBits.query IntegralMixedScalarQueryBits.commonLeading
  split_ifs <;> simp only [ContextEq, IntegralMixedRoutineTaskBits.query_get, reduceCtorEq, ite_false]

theorem homogeneous_context (P : Parameters) (F : Family) (q : List Bool) : ContextEq P q (IntegralMixedValueHomogeneousQueries.query P F q) := by
  unfold IntegralMixedValueHomogeneousQueries.query
  split_ifs
  · exact context_of_saved P q _ (IntegralMixedValueHomogeneousQueries.originalTask_saved P F q)
  · exact context_of_saved P q _ (IntegralMixedValueHomogeneousQueries.coordinateTask_saved P F q)

theorem reciprocal_context (P : Parameters) (F : Family) (q : List Bool) : ContextEq P q (IntegralMixedValueReciprocalTasks.query P F q) :=
  context_of_saved P q _ (IntegralMixedValueReciprocalTasks.query_saved P F q)
theorem macaulay_context (P : Parameters) (F : Family) (q : List Bool) : ContextEq P q (IntegralMixedValueMacaulayTasks.query P F q) :=
  context_of_saved P q _ (IntegralMixedValueMacaulayTasks.query_saved P F q)
theorem product_context (P : Parameters) (F : Family) (left : Bool) (q : List Bool) : ContextEq P q (IntegralMixedValueGramProductTasks.query P F left q) :=
  context_of_saved P q _ (IntegralMixedValueGramProductTasks.query_saved P F left q)
theorem sum_context (P : Parameters) (q : List Bool) (k : ℕ) : ContextEq P q (IntegralMixedValueGramSumTasks.query P (pair q (BinaryNatCode.encode k))) :=
  context_of_saved P q _ (IntegralMixedValueGramSumTasks.query_saved P q k)
end LeanCanny.Algebra.IntegralMixedValueRowContextBits
