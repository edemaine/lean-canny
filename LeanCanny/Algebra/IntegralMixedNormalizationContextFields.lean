/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationReplies
public import LeanCanny.Computation.NativeRequestInvariant
/-! # Normalization query writers retain their creating context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

def ContextEq (P : Parameters) (q c : List Bool) : Prop := get P .slot15 c = get P .slot15 q

theorem matrix_context (P : Parameters) (p : Phase) (z : List Bool) :
    get P .slot15 (IntegralCriticalFlatMatrixQuery.writer P p z) = get P .slot15 (pairFst z) := by
  simp only [IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false]
theorem next_context (P : Parameters) (p : Phase) (q : List Bool) : ContextEq P q (IntegralCriticalFlatEulerBits.next P p q) :=
  IntegralCriticalFlatEulerBits.next_get P p q .slot15

theorem field_context (P : Parameters) (parent : List Bool → List Bool) (p : Phase) (m k : List Bool → ℕ) (z : List Bool) :
    get P .slot15 (IntegralMixedNormalizationFieldBits.query P parent p m k z) = get P .slot15 (parent z) := by
  simp only [IntegralMixedNormalizationFieldBits.query_get, reduceCtorEq, ite_false]
theorem value_field_context (P : Parameters) (parent : List Bool → List Bool) (r : IntegralMixedRoutineTaskBits.Routine)
    (p : Phase) (f : Field) (v : List Bool → ℕ) (z : List Bool) (hf : f ≠ .slot15) :
    get P .slot15 (IntegralMixedValueFieldQuery.query P parent r p f v z) = get P .slot15 (parent z) := by
  simp only [IntegralMixedValueFieldQuery.query_get, reduceCtorEq, ite_false, Ne.symm hf]
theorem raw_context (P : Parameters) (F : Family) (q : List Bool) : ContextEq P q (rawQuery P F q) := by
  simp only [ContextEq, rawQuery_get, reduceCtorEq, ite_false]
theorem entry_context (P : Parameters) (p : Phase) (z : List Bool) : get P .slot15 (entryTask P p z) = get P .slot15 (original z) := by
  simp only [entryTask, matrix_context, pairFst_pair]
theorem moment_context (P : Parameters) (z : List Bool) : get P .slot15 (momentTask P z) = get P .slot15 (original z) := by
  simp only [momentTask, IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatBerkowitzQuery.momentWriter_get,
    reduceCtorEq, ite_false]
theorem routed_context (P : Parameters) (S : IntegralBerkowitzBlockBits.Source) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (z : List Bool) :
    get P .slot15 (IntegralMixedNormalizationMomentTasks.task P S route z) = get P .slot15 (original z) := by
  unfold IntegralMixedNormalizationMomentTasks.task
  rw [Function.comp_apply, Function.comp_apply, entry_context,
    IntegralMixedNormalizationMomentTasks.task_parent P route hr]
theorem factor_context (P : Parameters) (F : Family) (q : List Bool) : ContextEq P q ((factorProgram P F).query q) := by
  unfold ContextEq
  rw [factor_query]
  split_ifs
  · unfold diagonalChild
    rw [entry_context, diagonal_parent]
  · unfold momentChild
    rw [moment_context, outer_parent]

theorem small_context (P : Parameters) (z : List Bool) : get P .slot15 (smallTask P z) = get P .slot15 (pairFst z) :=
  field_context P pairFst .productPower _ _ z
theorem zero_context (P : Parameters) (z : List Bool) : get P .slot15 (zeroTask P z) = get P .slot15 (pairFst z) :=
  field_context P pairFst .originalGridTerm _ _ z
theorem index_context (P : Parameters) (F : Family) (q : List Bool) : ContextEq P q (indexTask P F q) :=
  field_context P id .clearedGridSum _ _ q
theorem inverse_context (P : Parameters) (z : List Bool) : get P .slot15 (inverseTask P z) = get P .slot15 (pairFst z) :=
  field_context P pairFst .productPower _ _ z
theorem leading_context (P : Parameters) (z : List Bool) : get P .slot15 (leadingTask P z) = get P .slot15 (pairFst z) :=
  field_context P pairFst .productPower _ _ z
theorem term_context (P : Parameters) (z : List Bool) : get P .slot15 (termTask P z) = get P .slot15 (pairFst z) :=
  value_field_context P pairFst .normalization .frozenPowerSum .target _ z (by decide)
theorem product_loop_context (P : Parameters) (z : List Bool) : get P .slot15 (productLoopTask P z) = get P .slot15 (pairFst z) :=
  value_field_context P pairFst .normalization .frozenLower .target _ z (by decide)
theorem product_left_context (P : Parameters) (q : List Bool) : ContextEq P q (productLeft P q) :=
  value_field_context P id .normalization .frozenConstant .col _ q (by decide)
theorem product_right_context (P : Parameters) (z : List Bool) : get P .slot15 (productRight P z) = get P .slot15 (pairFst z) :=
  value_field_context P pairFst .rawFactor .companion .row _ z (by decide)
end LeanCanny.Algebra.IntegralMixedNormalizationContextBits
