/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualMomentEntry
public import LeanCanny.Algebra.IntegralMixedNativeAction
/-! # Native virtual augmented entries and actual moment-power replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch IntegralCriticalFlatMomentTasks
open IntegralBerkowitzBlockBits (original)
set_option backward.isDefEq.respectTransparency false

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

theorem frame21 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool) (hp : isPhase .momentEntry q)
    (hc : (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F) (characteristicAccess P a F h)).controller.Requests answer budget q c) :
    IntegralMixedRoutineTaskBits.Frame P q c := by
  apply IntegralMixedMatrixFrames.frame_of_ordinary
  · obtain ⟨hg, hchild⟩ := (MatrixMoment.EntryBits.program_requests_iff
      (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F) (characteristicAccess P a F h))
      (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F))
      (rowTask P (characteristic P F)) (columnTask P (characteristic P F)) (matrixTask P (characteristic P F)) answer budget q c).mp hc
    rcases MatrixMoment.EntryBits.routed_cases
      (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F) (characteristicAccess P a F h))
      (rowTask P (characteristic P F)) (columnTask P (characteristic P F)) (matrixTask P (characteristic P F))
      (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q) hg with hr | hk | hm
    · rw [hchild, hr]
      exact moment_routed_routine P (characteristic P F) (IntegralBerkowitzBlockBits.rowQuery (characteristic P F)) (row_parent _) q _
    · rw [hchild, hk]
      exact moment_routed_routine P (characteristic P F) (IntegralBerkowitzBlockBits.columnQuery (characteristic P F)) (column_parent _) q _
    · rw [hchild, hm]
      exact moment_routed_routine P (characteristic P F) (IntegralBerkowitzBlockBits.matrixQuery (characteristic P F)) (matrix_parent _) q _
  · exact IntegralCriticalFlatMomentEntryBits.requests_frame P a (characteristic P F) (characteristicAccess P a F h) answer budget q c hp hc

noncomputable def stage21 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  ofSingleCall (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F) (characteristicAccess P a F h))
    ((IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F) (characteristicAccess P a F h)).certificates
      (IntegralCriticalFlatMomentEntryBits.controls P a (characteristic P F) (characteristicAccess P a F h)))
    (selected P .momentEntry) (selected_FP P a .momentEntry) (momentEntry P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem correct21 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (he : ∀ q, selected P .momentEntry q = true → IntegralCriticalFlatMomentEntryBits.RepliesAt P a
      (characteristic P F) (characteristicAccess P a F h) (fun q => residueBits (x q)) q) :
    Correct (stage21 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    exact value21 P a F h _ q (he q hq)
  · intro q hq hr
    let C := IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F) (characteristicAccess P a F h)
    have HC : C.controller.Requests (fun q => residueBits (x q)) (fun _ => 1) q (C.query q) := (C.requests_iff _ _ _ _).mpr ⟨hr, rfl⟩
    have HF := frame21 P a F h _ (fun _ => 1) q (C.query q) ((selected_iff P .momentEntry q).mp hq).2.2 HC
    have HE : IntegralCriticalHistoryEvaluator.residueWidth P (C.query q) = IntegralCriticalHistoryEvaluator.residueWidth P q :=
      congrArg (fun r => (numericCap P r).size) HF.1
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (C.query q)).trans_eq HE
  · intro q c budget hq hc
    exact frame21 P a F h _ budget q c ((selected_iff P .momentEntry q).mp hq).2.2 hc

abbrev MomentMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → isPhase .momentEntry q → answer q = momentEntry P F q

theorem moment_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : MomentMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1) :
    IntegralCriticalFlatMomentBits.RepliesAt P (characteristic P F) answer q := by
  intro i j
  let c := IntegralCriticalFlatMatrixQuery.writer P .momentEntry (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HC : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid
    simp only [c, IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P c = 1 := by simpa only [c, IntegralMixedMatrixFrames.matrix_routine, pairFst_pair] using hr
  have HP : isPhase .momentEntry c := IntegralCriticalFlatMatrixQuery.writer_phase P .momentEntry _
  exact (hx c HC HR HP).trans (moment_entry_child P F g q hv i j)

theorem correct22_of_matches (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool) (hx : MomentMatches P F answer) :
    Correct (stage22 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply correct22 P a F h answer
  intro q hq
  have H := (selected_iff P .momentPower q).mp hq
  exact moment_replies P F g answer hx q H.1 H.2.1

end LeanCanny.Algebra.IntegralMixedVirtualUpperBits
