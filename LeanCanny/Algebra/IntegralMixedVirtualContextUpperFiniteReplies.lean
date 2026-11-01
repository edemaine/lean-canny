/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextUpperReplyMatching
/-! # Finite virtual reduction and moment requests have actual component replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextUpperReplyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualContextUpperBits IntegralMixedVirtualContextComponentBits
open IntegralBerkowitzBlockBits IntegralCriticalFlatMomentTasks
set_option backward.isDefEq.respectTransparency false

theorem entry_current (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hm : Matches P F answer) (hl : LeadingCallback P F answer)
    (q : List Bool) (hq : selected P .reductionEntry q = true) : EntryRepliesAt P F answer q := by
  have H := selected_base P .reductionEntry q hq
  have HX := ((IntegralMixedVirtualContextBits.selected_iff P .reductionEntry q).mp hq).2
  refine ⟨hl q (Or.inr hq), ?_⟩
  let p := IntegralMixedVirtualLowerChildBits.input P F q
  have HP : original p = q := IntegralMixedVirtualLowerChildBits.input_parent P F q
  apply current P F answer hm .eulerLower (by decide) q _
  · exact (IntegralCriticalFlatLowerQuery.writer_root P p).trans (congrArg RankedHistoryTask.root HP)
  · exact (IntegralCriticalFlatLowerQuery.writer_birth P p).trans (congrArg (birth P) HP)
  · unfold IntegralMixedVirtualLowerChildBits.child IntegralMixedRoutineTaskBits.routine
    simp only [IntegralCriticalFlatLowerQuery.writer_get, reduceCtorEq, ite_false, IntegralMixedVirtualLowerChildBits.input_parent]
  · unfold IntegralMixedVirtualLowerChildBits.child
    simp only [IntegralCriticalFlatLowerQuery.writer_get, reduceCtorEq, ite_false, IntegralMixedVirtualLowerChildBits.input_parent]
  · exact H.1
  · exact H.2.1
  · exact HX
  · exact IntegralCriticalFlatLowerQuery.writer_phase P p

theorem moment_current (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hm : Matches P F answer)
    (q : List Bool) (hq : selected P .momentPower q = true) :
    IntegralCriticalFlatMomentBits.RepliesAt P (IntegralMixedVirtualUpperBits.characteristic P F) answer q := by
  intro i j
  have H := selected_base P .momentPower q hq
  have HX := ((IntegralMixedVirtualContextBits.selected_iff P .momentPower q).mp hq).2
  have HM := matrix P F answer hm .momentEntry (by decide)
    (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
    (by simpa only [pairFst_pair] using H.1) (by simpa only [pairFst_pair] using H.2.1) (by simpa only [pairFst_pair] using HX)
  exact HM.trans (IntegralMixedVirtualUpperBits.moment_entry_child P F g q H.1 i j)

theorem moment_task_current (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hm : Matches P F answer) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (q v : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hq : IntegralMixedRoutineTaskBits.routine P q = 1)
    (hx : IntegralMixedVirtualContextBits.context P q) :
    answer (task P (IntegralMixedVirtualUpperBits.characteristic P F) route (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (IntegralMixedVirtualUpperBits.characteristic P F) q)) v)) =
      IntegralMixedVirtualMatrixBits.actionEntry P F
        (task P (IntegralMixedVirtualUpperBits.characteristic P F) route (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (IntegralMixedVirtualUpperBits.characteristic P F) q)) v)) := by
  let p := pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (IntegralMixedVirtualUpperBits.characteristic P F) q)) v
  let z := route (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P) p)
  have HP : original p = q := IntegralCriticalFlatMomentEntryBits.request_parent P (IntegralMixedVirtualUpperBits.characteristic P F) q v
  have HZ : original z = q := (task_parent P route hr p).trans HP
  change answer (IntegralCriticalFlatMatrixQuery.writer P .actionEntry (IntegralCriticalFlatBerkowitzQuery.entryPacket (IntegralMixedVirtualUpperBits.characteristic P F) z)) = _
  exact matrix P F answer hm .actionEntry (by decide) _
    (by rw [IntegralCriticalFlatBerkowitzQuery.entry_parent, HZ]; exact hv)
    (by rw [IntegralCriticalFlatBerkowitzQuery.entry_parent, HZ]; exact hq)
    (by rw [IntegralCriticalFlatBerkowitzQuery.entry_parent, HZ]; exact hx)

theorem action_current (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (answer : List Bool → List Bool)
    (hm : Matches P F answer) (q : List Bool) (hq : selected P .momentEntry q = true) :
    MomentEntryRepliesAt P a F h answer q := by
  intro hg
  have H := selected_base P .momentEntry q hq
  have HX := ((IntegralMixedVirtualContextBits.selected_iff P .momentEntry q).mp hq).2
  have HG : MatrixMoment.EntryBits.entry (MatrixMoment.EntryBits.marked
      (IntegralCriticalFlatMomentEntryBits.bits P a (IntegralMixedVirtualUpperBits.characteristic P F) (IntegralMixedVirtualUpperBits.characteristicAccess P a F h)))
      (IntegralCriticalFlatMomentEntryBits.input P (IntegralMixedVirtualUpperBits.characteristic P F) q) = [true] := of_decide_eq_true hg
  rcases MatrixMoment.EntryBits.routed_cases
    (IntegralCriticalFlatMomentEntryBits.bits P a (IntegralMixedVirtualUpperBits.characteristic P F) (IntegralMixedVirtualUpperBits.characteristicAccess P a F h))
    (rowTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (columnTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (matrixTask P (IntegralMixedVirtualUpperBits.characteristic P F))
    (IntegralCriticalFlatMomentEntryBits.input P (IntegralMixedVirtualUpperBits.characteristic P F) q) HG with hr | hc | hm'
  · change answer (MatrixMoment.EntryBits.entry (MatrixMoment.EntryBits.routed
      (IntegralCriticalFlatMomentEntryBits.bits P a (IntegralMixedVirtualUpperBits.characteristic P F) (IntegralMixedVirtualUpperBits.characteristicAccess P a F h))
      (rowTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (columnTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (matrixTask P (IntegralMixedVirtualUpperBits.characteristic P F)))
      (IntegralCriticalFlatMomentEntryBits.input P (IntegralMixedVirtualUpperBits.characteristic P F) q)) = IntegralMixedVirtualMatrixBits.actionEntry P F (MatrixMoment.EntryBits.entry (MatrixMoment.EntryBits.routed
      (IntegralCriticalFlatMomentEntryBits.bits P a (IntegralMixedVirtualUpperBits.characteristic P F) (IntegralMixedVirtualUpperBits.characteristicAccess P a F h))
      (rowTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (columnTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (matrixTask P (IntegralMixedVirtualUpperBits.characteristic P F)))
      (IntegralCriticalFlatMomentEntryBits.input P (IntegralMixedVirtualUpperBits.characteristic P F) q))
    rw [hr]
    exact moment_task_current P F answer hm (rowQuery (IntegralMixedVirtualUpperBits.characteristic P F)) (row_parent _) q _ H.1 H.2.1 HX
  · change answer (MatrixMoment.EntryBits.entry (MatrixMoment.EntryBits.routed
      (IntegralCriticalFlatMomentEntryBits.bits P a (IntegralMixedVirtualUpperBits.characteristic P F) (IntegralMixedVirtualUpperBits.characteristicAccess P a F h))
      (rowTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (columnTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (matrixTask P (IntegralMixedVirtualUpperBits.characteristic P F)))
      (IntegralCriticalFlatMomentEntryBits.input P (IntegralMixedVirtualUpperBits.characteristic P F) q)) = IntegralMixedVirtualMatrixBits.actionEntry P F (MatrixMoment.EntryBits.entry (MatrixMoment.EntryBits.routed
      (IntegralCriticalFlatMomentEntryBits.bits P a (IntegralMixedVirtualUpperBits.characteristic P F) (IntegralMixedVirtualUpperBits.characteristicAccess P a F h))
      (rowTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (columnTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (matrixTask P (IntegralMixedVirtualUpperBits.characteristic P F)))
      (IntegralCriticalFlatMomentEntryBits.input P (IntegralMixedVirtualUpperBits.characteristic P F) q))
    rw [hc]
    exact moment_task_current P F answer hm (columnQuery (IntegralMixedVirtualUpperBits.characteristic P F)) (column_parent _) q _ H.1 H.2.1 HX
  · change answer (MatrixMoment.EntryBits.entry (MatrixMoment.EntryBits.routed
      (IntegralCriticalFlatMomentEntryBits.bits P a (IntegralMixedVirtualUpperBits.characteristic P F) (IntegralMixedVirtualUpperBits.characteristicAccess P a F h))
      (rowTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (columnTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (matrixTask P (IntegralMixedVirtualUpperBits.characteristic P F)))
      (IntegralCriticalFlatMomentEntryBits.input P (IntegralMixedVirtualUpperBits.characteristic P F) q)) = IntegralMixedVirtualMatrixBits.actionEntry P F (MatrixMoment.EntryBits.entry (MatrixMoment.EntryBits.routed
      (IntegralCriticalFlatMomentEntryBits.bits P a (IntegralMixedVirtualUpperBits.characteristic P F) (IntegralMixedVirtualUpperBits.characteristicAccess P a F h))
      (rowTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (columnTask P (IntegralMixedVirtualUpperBits.characteristic P F)) (matrixTask P (IntegralMixedVirtualUpperBits.characteristic P F)))
      (IntegralCriticalFlatMomentEntryBits.input P (IntegralMixedVirtualUpperBits.characteristic P F) q))
    rw [hm']
    exact moment_task_current P F answer hm (matrixQuery (IntegralMixedVirtualUpperBits.characteristic P F)) (matrix_parent _) q _ H.1 H.2.1 HX
end LeanCanny.Algebra.IntegralMixedVirtualContextUpperReplyBits
