/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramRelativeValue
public import LeanCanny.Algebra.IntegralMixedGramMomentMatches
/-! # Native relative-factor entries request actual action and moment values -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits NativeControllerBranch

theorem frame_of_tasks_same_routine (P : Parameters) (q c : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P c = IntegralMixedRoutineTaskBits.routine P q)
    (ht : Tasks P q c) (hd : IntegralCriticalHistoryTask.rank P c < IntegralCriticalHistoryTask.rank P q) :
    IntegralMixedRoutineTaskBits.Frame P q c := by
  rcases ht with rfl | ht
  · exact False.elim (Nat.lt_irrefl _ hd)
  · exact IntegralMixedMatrixFrames.frame_of_ordinary P q c hr ⟨ht.1, ht.2, hd⟩

noncomputable def factorSize (P : Parameters) (F : Family) (q : List Bool) : ℕ := powerDimension (characteristic P F) q
theorem factorSize_binary (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    BinaryFn (factorSize P F) :=
  (((characteristicAccess P a F h).dimension.add (BinaryFn.const 1)).mul
    ((characteristicAccess P a F h).dimension.add (BinaryFn.const 1))).mul (characteristicAccess P a F h).rank

theorem frame23 (P : Parameters) (F : Family) (answer : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hp : isPhase .relativeFactor q)
    (hc : (IntegralCriticalFlatRelativeFactorBits.program P (characteristic P F)).controller.Requests answer budget q c) :
    IntegralMixedRoutineTaskBits.Frame P q c := by
  apply frame_of_tasks_same_routine P q c
  · obtain ⟨_, hchild⟩ := (SingleCall.Program.requery_requests_iff
      (entryController (characteristic P F) (IntegralCriticalFlatBerkowitzQuery.entryWriter P (characteristic P F))
        (IntegralCriticalFlatBerkowitzQuery.momentWriter P))
      (IntegralCriticalFlatRelativeFactorBits.packet P) answer budget q c).mp hc
    simp only [entryController, IntegralBerkowitzBlockBits.program] at hchild
    unfold IntegralBerkowitzBlockBits.child at hchild
    split_ifs at hchild
    · rw [hchild]
      unfold IntegralCriticalFlatBerkowitzQuery.entryWriter
      simp only [Function.comp_apply, IntegralMixedMatrixFrames.matrix_routine, IntegralCriticalFlatBerkowitzQuery.entry_parent,
        IntegralCriticalFlatRelativeFactorBits.diagonal_original, IntegralCriticalFlatRelativeFactorBits.outer_original]
    · rw [hchild]
      unfold IntegralMixedRoutineTaskBits.routine
      rw [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, IntegralCriticalFlatRelativeFactorBits.outer_original]
      rfl
  · exact IntegralCriticalFlatRelativeFactorBits.requests_tasks P (characteristic P F) answer budget q q c (tasks_self P q) hc
  · exact IntegralCriticalFlatRelativeFactorBits.requests_rank P (characteristic P F) answer budget q c hp hc

abbrev MomentPowerMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 3 → isPhase .momentPower q →
    answer q = momentValue P F q

theorem diagonalChild23_reply (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hx : ActionMatches P F answer) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 3) :
    answer (diagonalChild23 P F q) = IntegralMixedGramMatrixModel.actionValue P F (diagonalChild23 P F q) := by
  have HP : original (diagonalQuery (characteristic P F) (outer23 P F q)) = q :=
    (IntegralCriticalFlatRelativeFactorBits.diagonal_original _ _).trans (outer23_parent P F q)
  apply hx
  · unfold IntegralMixedVirtualCaps.valid diagonalChild23 IntegralCriticalFlatBerkowitzQuery.entryWriter
    simp only [Function.comp_apply, IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatMatrixQuery.writer_root,
      IntegralCriticalFlatBerkowitzQuery.entry_parent, HP]
    exact hv
  · simpa only [diagonalChild23, IntegralCriticalFlatBerkowitzQuery.entryWriter, Function.comp_apply,
      IntegralMixedMatrixFrames.matrix_routine, IntegralCriticalFlatBerkowitzQuery.entry_parent, HP] using hr
  · exact IntegralCriticalFlatMatrixQuery.writer_phase P .actionEntry _

theorem momentChild23_reply (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hx : MomentPowerMatches P F answer) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 3) :
    answer (momentChild23 P F q) = momentValue P F (momentChild23 P F q) := by
  apply hx
  · unfold IntegralMixedVirtualCaps.valid momentChild23
    rw [IntegralCriticalFlatBerkowitzQuery.momentWriter_birth, IntegralCriticalFlatBerkowitzQuery.momentWriter_root, outer23_parent]
    exact hv
  · unfold IntegralMixedRoutineTaskBits.routine momentChild23
    rw [IntegralCriticalFlatBerkowitzQuery.momentWriter_get, outer23_parent]
    simpa only [reduceCtorEq, ite_false, IntegralMixedRoutineTaskBits.routine] using hr
  · exact IntegralCriticalFlatBerkowitzQuery.momentWriter_phase P _

noncomputable def stage23 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  ofSingleCall (IntegralCriticalFlatRelativeFactorBits.program P (characteristic P F))
    ((IntegralCriticalFlatRelativeFactorBits.program P (characteristic P F)).certificates
      (IntegralCriticalFlatRelativeFactorBits.controls P a (characteristic P F) (characteristicAccess P a F h)))
    (selectedFinite P .relativeFactor (factorSize P F))
    (selectedFinite_FP P a .relativeFactor _ (factorSize_binary P a F h))
    (IntegralMixedGramMatrixModel.factorValue P F) (IntegralCriticalHistoryEvaluator.residueWidth P)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem correct23 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (ha : ActionMatches P F (fun q => residueBits (x q))) (hm : MomentPowerMatches P F (fun q => residueBits (x q))) :
    Correct (stage23 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    have H := (selectedFinite_iff P .relativeFactor (factorSize P F) q).mp hq
    exact value23 P a F h g _ q H.1.1
      (fun _ => diagonalChild23_reply P F _ ha q H.1.1 H.1.2.1)
      (fun _ => momentChild23_reply P F _ hm q H.1.1 H.1.2.1) ⟨_, H.2.1⟩ ⟨_, H.2.2⟩ rfl rfl
  · intro q hq hr
    let C := IntegralCriticalFlatRelativeFactorBits.program P (characteristic P F)
    have HC : C.controller.Requests (fun q => residueBits (x q)) (fun _ => 1) q (C.query q) :=
      (C.requests_iff _ _ _ _).mpr ⟨hr, rfl⟩
    have HF := frame23 P F _ (fun _ => 1) q (C.query q) ((selectedFinite_iff P .relativeFactor (factorSize P F) q).mp hq).1.2.2 HC
    have HE : IntegralCriticalHistoryEvaluator.residueWidth P (C.query q) = IntegralCriticalHistoryEvaluator.residueWidth P q :=
      congrArg (fun r => (numericCap P r).size) HF.1
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (C.query q)).trans_eq HE
  · intro q c budget hq hc
    exact frame23 P F _ budget q c ((selectedFinite_iff P .relativeFactor (factorSize P F) q).mp hq).1.2.2 hc

end LeanCanny.Algebra.IntegralMixedGramUpperBits
