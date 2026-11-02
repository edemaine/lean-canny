/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscMomentProgram
public import LeanCanny.Algebra.IntegralMixedPscContextDomain
/-! # Augmented PSC replies close against their actual phase-zero values -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscContextUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPscUpperBits
open IntegralMixedCutSource IntegralBerkowitzBlockBits IntegralMixedPscMomentTasks
open scoped Classical

abbrev ActionMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, selected P F .originalCoefficient q = true → answer q = IntegralMixedPscMatrixModel.actionValue P F q

theorem moment_task_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hx : ActionMatches P F answer) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (q v : List Bool) (hq : Domain P F q) :
    answer (task P (characteristic P F) route (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q)) v)) =
      IntegralMixedPscMatrixModel.actionValue P F
        (task P (characteristic P F) route (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q)) v)) := by
  let p := pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q)) v
  let z := route (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P) p)
  have HP : original p = q := IntegralCriticalFlatMomentEntryBits.request_parent P (characteristic P F) q v
  have HZ : original z = q := (task_parent P route hr p).trans HP
  apply hx
  apply decide_eq_true
  refine ⟨?_, ?_⟩
  · exact entryWriter_domain P F (characteristic P F) z (HZ.symm ▸ hq)
  · exact IntegralCriticalFlatMatrixQuery.writer_phase P .originalCoefficient _

theorem replies1_of_action (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : ActionMatches P F answer) (q : List Bool) (hq : Domain P F q) :
    MomentEntryRepliesAt P a F h answer q := by
  have H := action_replies1 P a F h g q hq.1
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2 h3
    exact (moment_task_matches P F answer hx (rowQuery (characteristic P F)) (row_parent _) q _ hq).trans (H.1 h1 h2 h3)
  · intro h1 h2 h3 h4
    exact (moment_task_matches P F answer hx (columnQuery (characteristic P F)) (column_parent _) q _ hq).trans (H.2.1 h1 h2 h3 h4)
  · intro h1 h2 h3 h4
    exact (moment_task_matches P F answer hx (matrixQuery (characteristic P F)) (matrix_parent _) q _ hq).trans (H.2.2 h1 h2 h3 h4)

end LeanCanny.Algebra.IntegralMixedPscContextUpperBits
