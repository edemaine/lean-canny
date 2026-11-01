/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscMomentMatches
public import LeanCanny.Algebra.IntegralCriticalHistoryEvaluator
/-! # Native PSC augmented entries use actual phase-zero replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits NativeControllerBranch IntegralMixedPscMomentTasks
open scoped Classical
private theorem routed_frame1 (P : Parameters) (F : Family) (route : List Bool → List Bool)
    (hr : ∀ p, original (route p) = original (original p)) (q v : List Bool) (hp : isPhase .derivativeCoefficient q) :
    IntegralMixedRoutineTaskBits.Frame P q
      (task P (characteristic P F) route (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q)) v)) := by
  have HP := IntegralCriticalFlatMomentEntryBits.request_parent P (characteristic P F) q v
  have HF := task_frame P (characteristic P F) route hr
    (pair (pairFst (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q)) v)
    (by rw [HP]; change phase q = 1 at hp; omega)
  simpa only [HP] using HF

theorem frame1 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool) (hp : isPhase .derivativeCoefficient q)
    (hc : (momentEntryProgram P a F h).controller.Requests answer budget q c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  obtain ⟨hg, hchild⟩ := (MatrixMoment.EntryBits.program_requests_iff
    (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F) (characteristicAccess P a F h))
    (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F))
    (rowTask P (characteristic P F)) (columnTask P (characteristic P F)) (matrixTask P (characteristic P F)) answer budget q c).mp hc
  rcases MatrixMoment.EntryBits.routed_cases
    (IntegralCriticalFlatMomentEntryBits.bits P a (characteristic P F) (characteristicAccess P a F h))
    (rowTask P (characteristic P F)) (columnTask P (characteristic P F)) (matrixTask P (characteristic P F))
    (IntegralCriticalFlatMomentEntryBits.input P (characteristic P F) q) hg with hr | hk | hm
  · rw [hchild, hr]
    exact routed_frame1 P F (rowQuery (characteristic P F)) (row_parent _) q _ hp
  · rw [hchild, hk]
    exact routed_frame1 P F (columnQuery (characteristic P F)) (column_parent _) q _ hp
  · rw [hchild, hm]
    exact routed_frame1 P F (matrixQuery (characteristic P F)) (matrix_parent _) q _ hp

def Selected1 (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  Domain P F q ∧ isPhase .derivativeCoefficient q ∧ get P .row q < IntegralMixedPscMomentMatrix.size P F q ∧
    get P .col q < IntegralMixedPscMomentMatrix.size P F q
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (Selected1 P F q) := inferInstanceAs (Decidable (_ ∧ _))
theorem moment_size_binary (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    BinaryFn (IntegralMixedPscMomentMatrix.size P F) :=
  ((momentAccess P a F h).dimension.add (BinaryFn.const 2)).mul (momentAccess P a F h).rank

theorem selected1_FP (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) : FPPred (Selected1 P F) :=
  (domain_FP P a F h).and ((isPhase_FP .derivativeCoefficient).and
    (((get_binary P a .row).lt (moment_size_binary P a F h)).and ((get_binary P a .col).lt (moment_size_binary P a F h))))

noncomputable def stage1 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  ofSingleCall (momentEntryProgram P a F h) ((momentEntryProgram P a F h).certificates (momentEntry_controls P a F h))
    (fun q => decide (Selected1 P F q)) (selected1_FP P a F h).flag_mem_FP (entryValue P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem correct1 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hx : ActionMatches P F (fun q => residueBits (x q))) :
    Correct (stage1 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  unfold stage1
  apply ofSingleCall_correct
  · intro q hq
    have HS : Selected1 P F q := of_decide_eq_true hq
    have HE := value1 P a F h _ q (replies1_of_action P a F h g _ hx q HS.1)
    simpa only [entryValue, momentEntry, Nat.mod_eq_of_lt HS.2.2.1, Nat.mod_eq_of_lt HS.2.2.2] using HE
  · intro q hq hr
    have HS : Selected1 P F q := of_decide_eq_true hq
    let C := momentEntryProgram P a F h
    have HC : C.controller.Requests (fun q => residueBits (x q)) (fun _ => 1) q (C.query q) :=
      (C.requests_iff _ _ _ _).mpr ⟨hr, rfl⟩
    have HF := frame1 P a F h _ (fun _ => 1) q (C.query q) HS.2.1 HC
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (C.query q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) HF.1)
  · intro q c budget hq hc
    have HS : Selected1 P F q := of_decide_eq_true hq
    exact frame1 P a F h _ budget q c HS.2.1 hc

end LeanCanny.Algebra.IntegralMixedPscUpperBits
