/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramMomentReplies
public import LeanCanny.Algebra.IntegralMixedMatrixFrames
/-! # Native augmented entries use the actual action branch -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits IntegralCriticalFlatMomentTasks NativeControllerBranch

theorem moment_task_routine (P : Parameters) (S : IntegralBerkowitzBlockBits.Source) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (p : List Bool) :
    IntegralMixedRoutineTaskBits.routine P (task P S route p) = IntegralMixedRoutineTaskBits.routine P (original p) := by
  unfold task IntegralCriticalFlatBerkowitzQuery.entryWriter
  simp only [Function.comp_apply, IntegralMixedMatrixFrames.matrix_routine, IntegralCriticalFlatBerkowitzQuery.entry_parent,
    task_parent P route hr p]

theorem moment_routed_routine (P : Parameters) (S : IntegralBerkowitzBlockBits.Source) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (q v : List Bool) :
    IntegralMixedRoutineTaskBits.routine P (task P S route (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P S q)) v)) =
      IntegralMixedRoutineTaskBits.routine P q := by
  rw [moment_task_routine P S route hr, IntegralCriticalFlatMomentEntryBits.request_parent]

abbrev ActionMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 3 → isPhase .actionEntry q →
    answer q = IntegralMixedGramMatrixModel.actionValue P F q

theorem moment_task_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hx : ActionMatches P F answer) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (q v : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hq : IntegralMixedRoutineTaskBits.routine P q = 3) :
    answer (task P (characteristic P F) route (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q)) v)) =
      IntegralMixedGramMatrixModel.actionValue P F
        (task P (characteristic P F) route (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q)) v)) := by
  let p := pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q)) v
  let z := route (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P) p)
  have HP : original p = q := IntegralCriticalFlatMomentEntryBits.request_parent P (characteristic P F) q v
  have HZ : original z = q := (task_parent P route hr p).trans HP
  apply hx
  · unfold IntegralMixedVirtualCaps.valid task IntegralCriticalFlatBerkowitzQuery.entryWriter
    simp only [Function.comp_apply, IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatMatrixQuery.writer_root,
      IntegralCriticalFlatBerkowitzQuery.entry_parent]
    change birth P (original z) < P.cap (RankedHistoryTask.root (original z))
    rw [HZ]
    exact hv
  · exact (moment_routed_routine P (characteristic P F) route hr q v).trans hq
  · exact IntegralCriticalFlatMatrixQuery.writer_phase P .actionEntry _

theorem moment_replies_of_action (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : ActionMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 3) :
    IntegralCriticalFlatMomentEntryBits.RepliesAt P a (characteristic P F) (characteristicAccess P a F h) answer q := by
  have H := action_replies21 P a F h g q hv
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2 h3
    exact (moment_task_matches P F answer hx (rowQuery (characteristic P F)) (row_parent _) q _ hv hr).trans (H.1 h1 h2 h3)
  · intro h1 h2 h3 h4
    exact (moment_task_matches P F answer hx (columnQuery (characteristic P F)) (column_parent _) q _ hv hr).trans (H.2.1 h1 h2 h3 h4)
  · intro h1 h2 h3 h4
    exact (moment_task_matches P F answer hx (matrixQuery (characteristic P F)) (matrix_parent _) q _ hv hr).trans (H.2.2 h1 h2 h3 h4)

end LeanCanny.Algebra.IntegralMixedGramUpperBits
