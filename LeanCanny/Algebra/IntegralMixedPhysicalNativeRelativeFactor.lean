/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalRelativeValue
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeMomentEntry
/-! # Native relative-factor entries request actual action and moment values -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralBerkowitzBlockBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def factorSize (P : Parameters) (F : Family) (q : List Bool) : ℕ := powerDimension (characteristic P F) q
theorem factorSize_binary (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F) :
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

abbrev RelativeFactorRepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  (selector (characteristic P F) (outer23 P F q) = [false, true] →
    answer (diagonalChild23 P F q) = IntegralMixedPhysicalMatrixBits.actionEntry P F (diagonalChild23 P F q)) ∧
  (selector (characteristic P F) (outer23 P F q) = [true, true] →
    answer (momentChild23 P F q) = momentValue P F (momentChild23 P F q))

noncomputable def stage23 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : Machine :=
  ofSingleCall (IntegralCriticalFlatRelativeFactorBits.program P (characteristic P F))
    ((IntegralCriticalFlatRelativeFactorBits.program P (characteristic P F)).certificates
      (IntegralCriticalFlatRelativeFactorBits.controls P a (characteristic P F) (characteristicAccess P a F h)))
    (selectedFinite P .relativeFactor (factorSize P F))
    (selectedFinite_FP P a .relativeFactor _ (factorSize_binary P a F h))
    (IntegralMixedPhysicalMatrixBits.relativeFactor P F) (IntegralCriticalHistoryEvaluator.residueWidth P)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem correct23 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (he : ∀ q, selectedFinite P .relativeFactor (factorSize P F) q = true → RelativeFactorRepliesAt P F (fun q => residueBits (x q)) q) :
    Correct (stage23 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    have HSEL := (selectedFinite_iff P .relativeFactor (factorSize P F) q).mp hq
    have H := selected_base P .relativeFactor q HSEL.1
    exact value23 P a F h g _ q (he q hq).1 (he q hq).2 ⟨_, HSEL.2.1⟩ ⟨_, HSEL.2.2⟩ rfl rfl
  · intro q hq hr
    let C := IntegralCriticalFlatRelativeFactorBits.program P (characteristic P F)
    have HC : C.controller.Requests (fun q => residueBits (x q)) (fun _ => 1) q (C.query q) :=
      (C.requests_iff _ _ _ _).mpr ⟨hr, rfl⟩
    have HF := frame23 P F _ (fun _ => 1) q (C.query q) (selected_base P .relativeFactor q ((selectedFinite_iff P .relativeFactor (factorSize P F) q).mp hq).1).2.2 HC
    have HE : IntegralCriticalHistoryEvaluator.residueWidth P (C.query q) = IntegralCriticalHistoryEvaluator.residueWidth P q :=
      congrArg (fun r => (numericCap P r).size) HF.1
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (C.query q)).trans_eq HE
  · intro q c budget hq hc
    exact frame23 P F _ budget q c (selected_base P .relativeFactor q ((selectedFinite_iff P .relativeFactor (factorSize P F) q).mp hq).1).2.2 hc

end LeanCanny.Algebra.IntegralMixedPhysicalUpperBits
