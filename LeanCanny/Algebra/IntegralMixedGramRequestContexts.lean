/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramUpperCorrect
public import LeanCanny.Algebra.IntegralMixedValueRowContextFields
/-! # Gram determinant requests retain the virtual creating context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedGramUpperBits IntegralBerkowitzBlockBits IntegralCriticalFlatMomentTasks
set_option backward.isDefEq.respectTransparency false
abbrev ContextEq := IntegralMixedValueRowContextBits.ContextEq

theorem matrix_context (P : Parameters) (p : Phase) (z : List Bool) :
    get P .slot15 (IntegralCriticalFlatMatrixQuery.writer P p z) = get P .slot15 (pairFst z) := by
  simp only [IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false]
theorem entry_context (P : Parameters) (S : IntegralBerkowitzBlockBits.Source) (z : List Bool) :
    get P .slot15 (IntegralCriticalFlatBerkowitzQuery.entryWriter P S z) = get P .slot15 (original z) := by
  unfold IntegralCriticalFlatBerkowitzQuery.entryWriter
  rw [Function.comp_apply, matrix_context, IntegralCriticalFlatBerkowitzQuery.entry_parent]
theorem moment_context (P : Parameters) (z : List Bool) :
    get P .slot15 (IntegralCriticalFlatBerkowitzQuery.momentWriter P z) = get P .slot15 (original z) := by
  simp only [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_false]
theorem routed_context (P : Parameters) (S : IntegralBerkowitzBlockBits.Source) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (z : List Bool) :
    get P .slot15 (task P S route z) = get P .slot15 (original z) := by
  unfold task
  rw [Function.comp_apply, Function.comp_apply, entry_context, task_parent P route hr]

variable (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
  (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool)
  (own : IntegralMixedGramUpperModel.Matches P F answer)
attribute [local irreducible] characteristic characteristicAccess IntegralMixedGramBlockEntryNative.program

theorem context19 : RequestsSatisfy (IntegralMixedGramBlockEntryNative.machine P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  obtain ⟨_, HE⟩ := ((IntegralMixedGramBlockEntryNative.program P F).requests_iff answer budget q c).mp hc
  simp only [IntegralMixedGramBlockEntryNative.program] at HE
  rw [HE]
  exact IntegralMixedValueRowContextBits.context_of_saved P q _ (IntegralMixedGramBlockEntryTasks.query_saved P F q)

theorem context21 : RequestsSatisfy (stage21 P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  obtain ⟨hg, hchild⟩ := (MatrixMoment.EntryBits.program_requests_iff
    (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F) (characteristicAccess P a F h))
    (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F))
    (rowTask P (characteristic P F)) (columnTask P (characteristic P F)) (matrixTask P (characteristic P F)) answer budget q c).mp hc
  rcases MatrixMoment.EntryBits.routed_cases
    (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F) (characteristicAccess P a F h))
    (rowTask P (characteristic P F)) (columnTask P (characteristic P F)) (matrixTask P (characteristic P F))
    (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q) hg with hr | hk | hm
  · rw [hchild, hr]
    exact (routed_context P (characteristic P F) (rowQuery (characteristic P F)) (row_parent _) _).trans
      (congrArg (get P .slot15) (IntegralCriticalFlatMomentEntryBits.request_parent P (characteristic P F) q _))
  · rw [hchild, hk]
    exact (routed_context P (characteristic P F) (columnQuery (characteristic P F)) (column_parent _) _).trans
      (congrArg (get P .slot15) (IntegralCriticalFlatMomentEntryBits.request_parent P (characteristic P F) q _))
  · rw [hchild, hm]
    exact (routed_context P (characteristic P F) (matrixQuery (characteristic P F)) (matrix_parent _) _).trans
      (congrArg (get P .slot15) (IntegralCriticalFlatMomentEntryBits.request_parent P (characteristic P F) q _))

include g own in
theorem context22 : RequestsSatisfy (stage22 P a F h) answer (ContextEq P) := by
  intro q hs budget c hc
  have H := (selected_iff P .momentPower q).mp hs
  have HR := moment_replies P F g answer (IntegralMixedGramUpperDispatcher.moment_matches P F answer own) q H.1 H.2.1
  obtain ⟨i, j, rfl⟩ := ModularRecursiveStage.requests_in_bounds_local
    (IntegralBlockMomentBits.powerAccess (IntegralCriticalFlatMomentBits.source P (characteristic P F))
      (IntegralCriticalFlatMomentBits.access P a (characteristic P F) (characteristicAccess P a F h)))
    (IntegralCriticalFlatMatrixQuery.writer P .momentEntry) answer q HR budget c hc
  exact (matrix_context P .momentEntry _).trans (congrArg (get P .slot15) (pairFst_pair _ _))

theorem context23 : RequestsSatisfy (stage23 P a F h) answer (ContextEq P) := by
  intro q _ budget c hc
  change get P .slot15 c = get P .slot15 q
  obtain ⟨_, he⟩ := (SingleCall.Program.requery_requests_iff
    (entryController (characteristic P F) (IntegralCriticalFlatBerkowitzQuery.entryWriter P (characteristic P F))
      (IntegralCriticalFlatBerkowitzQuery.momentWriter P))
    (IntegralCriticalFlatRelativeFactorBits.packet P) answer budget q c).mp hc
  simp only [entryController, IntegralBerkowitzBlockBits.program] at he
  unfold IntegralBerkowitzBlockBits.child at he
  split_ifs at he
  · rw [he]
    rw [entry_context, IntegralCriticalFlatRelativeFactorBits.diagonal_original, IntegralCriticalFlatRelativeFactorBits.outer_original]
  · rw [he]
    rw [moment_context, IntegralCriticalFlatRelativeFactorBits.outer_original]

include g own in
theorem context24 : RequestsSatisfy (stage24 P a F h) answer (ContextEq P) := by
  intro q hs budget c hc
  have H := (selectedFinite_iff P .relativePower (fun q => (characteristic P F).rank q) q).mp hs
  have HR := factor_replies P F g answer (IntegralMixedGramUpperDispatcher.factor_matches P F answer own) q H.1.1 H.1.2.1
  obtain ⟨i, j, rfl⟩ := IntegralBerkowitzBlockBits.RecursiveStage.requests_in_bounds_local
    (characteristic P F) (characteristicAccess P a F h) (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor) answer q HR budget c hc
  exact (matrix_context P .relativeFactor _).trans (congrArg (get P .slot15) (pairFst_pair _ _))

include g own in
theorem requests_context : RequestsSatisfy (IntegralMixedGramUpperDispatcher.machine P a F h) answer (ContextEq P) := by
  unfold IntegralMixedGramUpperDispatcher.machine
  apply requestsSatisfy_choose _ _ answer _ (context19 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context21 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context22 P a F h g answer own)
  apply requestsSatisfy_choose _ _ answer _ (context23 P a F h answer)
  apply requestsSatisfy_choose _ _ answer _ (context24 P a F h g answer own)
  exact requestsSatisfy_zero answer _
end LeanCanny.Algebra.IntegralMixedGramContextBits
