/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscContextMomentMatches
public import LeanCanny.Algebra.IntegralMixedPscNativeMomentEntry
/-! # PSC arithmetic preserves every actual virtual context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscContextUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits NativeControllerBranch IntegralMixedPscMomentTasks
open IntegralMixedPscUpperBits
open scoped Classical
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


end LeanCanny.Algebra.IntegralMixedPscContextUpperBits
