/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscMomentTasks
public import LeanCanny.Algebra.IntegralMixedPscUpperSelection
/-! # Fresh PSC arithmetic writers preserve the actual finite source header -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
open scoped Classical

theorem degree_transport (P : Parameters) (F : Family) (q z : List Bool)
    (hs : IntegralMixedVirtualTaskBits.saved P z = IntegralMixedVirtualTaskBits.saved P q) :
    IntegralMixedPscEntryBits.degree P F z = IntegralMixedPscEntryBits.degree P F q := by
  change IntegralMixedCoordinateSquarefree.coordinateDegree
    (F.spatial (IntegralMixedVirtualTaskBits.saved P z)) (F.rule (IntegralMixedVirtualTaskBits.saved P z)) = _
  rw [hs]
  rfl

theorem domain_transport (P : Parameters) (F : Family) (q z : List Bool) (hq : Domain P F q)
    (hr : RankedHistoryTask.root z = RankedHistoryTask.root q) (hb : birth P z = birth P q)
    (hg : IntegralMixedRoutineTaskBits.routine P z = 3) (hc : get P .slot15 z = get P .slot15 q)
    (hi : get P .slot8 z = get P .slot8 q) : Domain P F z := by
  refine ⟨?_, hg, hc.trans hq.2.2.1, ?_⟩
  · unfold IntegralMixedVirtualCaps.valid
    rw [hr, hb]
    exact hq.1
  · rw [hi, degree_transport P F q z (IntegralMixedVirtualTaskBits.saved_invariance P q z hr hb hc)]
    exact hq.2.2.2

theorem entryWriter_domain (P : Parameters) (F : Family) (S : Source) (z : List Bool)
    (hq : Domain P F (original z)) : Domain P F (IntegralMixedPscMomentTasks.entryWriter P S z) := by
  apply domain_transport P F (original z) _ hq
  · simp only [IntegralMixedPscMomentTasks.entryWriter, Function.comp_apply,
      IntegralCriticalFlatMatrixQuery.writer_root, IntegralCriticalFlatBerkowitzQuery.entry_parent]
  · simp only [IntegralMixedPscMomentTasks.entryWriter, Function.comp_apply,
      IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatBerkowitzQuery.entry_parent]
  · simpa only [IntegralMixedPscMomentTasks.entryWriter, Function.comp_apply,
      IntegralMixedMatrixFrames.matrix_routine, IntegralCriticalFlatBerkowitzQuery.entry_parent] using hq.2.1
  · simp only [IntegralMixedPscMomentTasks.entryWriter, Function.comp_apply,
      IntegralCriticalFlatMatrixQuery.writer_get, IntegralCriticalFlatBerkowitzQuery.entry_parent, reduceCtorEq, ite_false]
  · simp only [IntegralMixedPscMomentTasks.entryWriter, Function.comp_apply,
      IntegralCriticalFlatMatrixQuery.writer_get, IntegralCriticalFlatBerkowitzQuery.entry_parent, reduceCtorEq, ite_false]

theorem matrixWriter_domain (P : Parameters) (F : Family) (p : Phase) (z : List Bool)
    (hq : Domain P F (pairFst z)) : Domain P F (IntegralCriticalFlatMatrixQuery.writer P p z) := by
  apply domain_transport P F (pairFst z) _ hq
  · exact IntegralCriticalFlatMatrixQuery.writer_root P p z
  · exact IntegralCriticalFlatMatrixQuery.writer_birth P p z
  · simpa only [IntegralMixedMatrixFrames.matrix_routine] using hq.2.1
  · simp only [IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false]
  · simp only [IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false]

end LeanCanny.Algebra.IntegralMixedPscUpperBits
