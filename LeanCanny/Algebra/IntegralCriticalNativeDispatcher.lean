/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeCompiler
public import LeanCanny.Algebra.IntegralCriticalNativeLowerModelView
public import LeanCanny.Algebra.IntegralCriticalNativeUpperModel
public import Mathlib.Tactic.IntervalCases
/-! # A concrete native evaluator for every critical-history task -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
abbrev Primitive := IntegralCriticalNativeLowerDispatcherBits.Primitive

def lowerSelected (q : List Bool) : Bool := decide (phase q ≤ 16)

theorem lowerSelected_FP : (fun q => [lowerSelected q]) ∈ FP :=
  ((BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27)).le (BinaryFn.const 16)).flag_mem_FP

noncomputable def machine (F : Scripts) (h : Controls F) (a : Primitive F) : Machine :=
  ((IntegralCriticalNativeLowerDispatcherBits.machine F h a).withGuard lowerSelected lowerSelected_FP).choose
    (IntegralCriticalNativeUpperBits.machine F h)

private theorem choose_selected (M N : Machine) (s : List Bool → Bool)
    (hs : (fun q => [s q]) ∈ FP) (q : List Bool) :
    ((M.withGuard s hs).choose N).selected q = (s q || N.selected q) := rfl

private theorem choose_model (M N : Machine) (s : List Bool → Bool)
    (hs : (fun q => [s q]) ∈ FP) (q : List Bool) :
    ((M.withGuard s hs).choose N).model q = if s q then M.model q else N.model q := rfl

theorem machine_selected (F : Scripts) (h : Controls F) (a : Primitive F) (q : List Bool) :
    (machine F h a).selected q = true := by
  rw [machine, choose_selected, IntegralCriticalNativeUpperBits.machine_selected, Bool.or_true]

theorem correct (F : Scripts) (h : Controls F) (a : Primitive F) :
    Correct (machine F h a) (answer F (IntegralCriticalActualModelBits.residue F)) (Frame F) := by
  apply choose_correct
  · apply withGuard_correct
    · exact IntegralCriticalNativeLowerDispatcherBits.correct F h a _
        (IntegralCriticalNativeModelBits.lower_matches F) (IntegralCriticalNativeModelBits.upper_matches F).companion
    · intro q _
      exact IntegralCriticalNativeLowerDispatcherBits.machine_selected F h a q
  · exact IntegralCriticalNativeUpperBits.correct F h _ (IntegralCriticalNativeModelBits.upper_matches F)

private theorem decode_le (n : ℕ) (hn : n ≤ 26) : (IntegralCriticalActualModelBits.decode n).code = n := by
  interval_cases n <;> rfl

private theorem decoded_phase (q : List Bool) : isPhase (IntegralCriticalActualModelBits.decode (phase q)) q := by
  apply Eq.symm
  exact decode_le (phase q) (min_le_right _ _)

theorem model_value (F : Scripts) (h : Controls F) (a : Primitive F) (q : List Bool) :
    (machine F h a).model q = IntegralCriticalActualModelBits.value F q := by
  rw [machine, choose_model]
  by_cases hv : IntegralCriticalTotalCompanionBits.valid F q
  · let p := IntegralCriticalActualModelBits.decode (phase q)
    have HP : isPhase p q := decoded_phase q
    have HE : phase q = p.code := HP
    by_cases hq : phase q ≤ 16
    · have HS : lowerSelected q = true := decide_eq_true hq
      simp only [HS, ite_true]
      exact (IntegralCriticalNativeLowerDispatcherBits.model_phase F h a p q (by omega) hv HP).trans
        (IntegralCriticalActualModelBits.value_phase F p q hv HP).symm
    · have HS : lowerSelected q = false := decide_eq_false hq
      simp only [HS, Bool.false_eq_true, ite_false]
      exact (IntegralCriticalNativeUpperBits.model_phase F h p q (by omega) hv HP).trans
        (IntegralCriticalActualModelBits.value_phase F p q hv HP).symm
  · rw [IntegralCriticalNativeModelBits.invalid_value F q hv]
    split_ifs
    · exact IntegralCriticalNativeLowerDispatcherBits.model_invalid F h a q hv
    · exact IntegralCriticalNativeUpperBits.model_invalid F h q hv

theorem evaluator (F : Scripts) (h : Controls F) (a : Primitive F) :
    SpaceFunction (IntegralCriticalActualModelBits.value F) :=
  IntegralCriticalNativeCompilerBits.actual_evaluator F h (machine F h a)
    (correct F h a) (machine_selected F h a) (model_value F h a)

end LeanCanny.Algebra.IntegralCriticalNativeDispatcherBits
