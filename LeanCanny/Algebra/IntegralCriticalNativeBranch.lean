/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.NativeSingleCallBranch
public import LeanCanny.Algebra.IntegralCriticalFlatActualSources
public import LeanCanny.Algebra.IntegralCriticalHistoryEvaluator
/-! # Shared native branch guards and actual critical-task frames -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeBranchBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources
set_option backward.isDefEq.respectTransparency false

def Frame (F : Scripts) (q c : List Bool) : Prop :=
  RankedHistoryTask.root c = RankedHistoryTask.root q ∧ c.length ≤ wordBudget F.toParameters q ∧
    rank F.toParameters c < rank F.toParameters q

def selected (F : Scripts) (p : Phase) (q : List Bool) : Bool :=
  decide (IntegralCriticalTotalCompanionBits.valid F q ∧ isPhase p q)

theorem selected_FP (F : Scripts) (h : Controls F) (p : Phase) : (fun q => [selected F p q]) ∈ FP :=
  ((IntegralCriticalTotalCompanionBits.valid_FP F h.task).and (isPhase_FP p)).flag_mem_FP

theorem selected_iff (F : Scripts) (p : Phase) (q : List Bool) : selected F p q = true ↔
    IntegralCriticalTotalCompanionBits.valid F q ∧ isPhase p q := by simp only [selected, decide_eq_true_eq]

noncomputable def answer (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (q : List Bool) : List Bool :=
  residueBits (x q)

theorem answer_length (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (q c : List Bool) (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) :
    (answer F x c).length ≤ IntegralCriticalHistoryEvaluator.residueWidth F.toParameters q := by
  have H := IntegralCriticalHistoryEvaluator.answer_length F.toParameters x c
  have HE : IntegralCriticalHistoryEvaluator.residueWidth F.toParameters c =
      IntegralCriticalHistoryEvaluator.residueWidth F.toParameters q := congrArg (fun r => (numericCap F.toParameters r).size) hr
  exact H.trans_eq HE

end LeanCanny.Algebra.IntegralCriticalNativeBranchBits
