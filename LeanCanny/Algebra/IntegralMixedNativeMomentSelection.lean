/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualMomentReplies
public import LeanCanny.Algebra.IntegralMixedNativeMomentEntry
/-! # Native augmented entries use the actual action branch -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits IntegralCriticalFlatMomentTasks NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev ActionMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → isPhase .actionEntry q →
    answer q = IntegralMixedVirtualMatrixBits.actionEntry P F q

theorem moment_task_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hx : ActionMatches P F answer) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (q v : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hq : IntegralMixedRoutineTaskBits.routine P q = 1) :
    answer (task P (characteristic P F) route (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q)) v)) =
      IntegralMixedVirtualMatrixBits.actionEntry P F
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
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1) :
    IntegralCriticalFlatMomentEntryBits.RepliesAt P a (characteristic P F) (characteristicAccess P a F h) answer q := by
  have H := action_replies21 P a F h g q hv
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2 h3
    exact (moment_task_matches P F answer hx (rowQuery (characteristic P F)) (row_parent _) q _ hv hr).trans (H.1 h1 h2 h3)
  · intro h1 h2 h3 h4
    exact (moment_task_matches P F answer hx (columnQuery (characteristic P F)) (column_parent _) q _ hv hr).trans (H.2.1 h1 h2 h3 h4)
  · intro h1 h2 h3 h4
    exact (moment_task_matches P F answer hx (matrixQuery (characteristic P F)) (matrix_parent _) q _ hv hr).trans (H.2.2 h1 h2 h3 h4)

theorem correct21_of_matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q)) (hx : ActionMatches P F (fun q => residueBits (x q))) :
    Correct (stage21 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply correct21 P a F h x
  intro q hq
  have H := (selected_iff P .momentEntry q).mp hq
  exact moment_replies_of_action P a F h g _ hx q H.1 H.2.1

end LeanCanny.Algebra.IntegralMixedVirtualUpperBits
