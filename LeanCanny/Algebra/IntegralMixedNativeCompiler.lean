/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.NativeControllerCompiler
public import LeanCanny.Algebra.IntegralMixedRoutineTask
public import LeanCanny.Algebra.IntegralCriticalHistoryEvaluator
/-! # Native compilation of the mixed birth/routine/phase rank -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNativeCompilerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open NativeControllerBranch

def bounds (P : Parameters) (a : Access P) : FrameBounds where
  root := RankedHistoryTask.root
  word := wordBudget P
  rank := IntegralMixedRoutineTaskBits.rank P
  word_unary := wordBudget_unary P a
  rank_unary := IntegralMixedRoutineTaskBits.rank_unary P a
  word_eq _ _ h := wordBudget_eq P h

theorem evaluator (P : Parameters) (a : Access P) (M : Machine)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hc : Correct M (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P))
    (hs : ∀ q, M.selected q = true) (hv : ∀ q, M.model q = residueBits (x q)) :
    SpaceFunction (fun q => residueBits (x q)) :=
  evaluator_of_frames M (bounds P a) (fun q => residueBits (x q)) hc hs hv
    (IntegralCriticalHistoryEvaluator.residueWidth P)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)
    (IntegralCriticalHistoryEvaluator.answer_length P x)

end LeanCanny.Algebra.IntegralMixedNativeCompilerBits
