/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralEulerLowReaderSpace
public import LeanCanny.Computation.ControllerRequests

/-! # Recursive selection of actual Euler lower rows

The objective row requests its two-term objective stage. Every other row
requests the cleared gradient at the original spatial target. The adapter
for reduction queries preserves the saved source and both old basis ranks.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralEulerBits.LowerStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def program (S : Source) (i : ∀ c, Fin (S.free c))
    (objectiveTask gradientTask : List Bool → List Bool) : SingleCall.Program where
  request _ := true
  query c := if (i c).val = objectiveRank S c then objectiveTask c else gradientTask (lowerGradientQuery S i c)
  immediate _ := []
  finish := pairSnd

theorem controls (S : Source) (a : Access S) (i : ∀ c, Fin (S.free c))
    (hi : BinaryFn (fun c => (i c).val)) (objectiveTask gradientTask : List Bool → List Bool)
    (ho : objectiveTask ∈ FP) (hg : gradientTask ∈ FP) : (program S i objectiveTask gradientTask).Controls := by
  have HB : FPPred (fun c => (i c).val = objectiveRank S c) := hi.eq a.objective
  exact ⟨constFn_mem_FP [true], HB.ite_mem_FP ho
    (mem_FP_comp (lowerGradientQuery_FP S a i hi) hg), constFn_mem_FP [], pairSnd_mem_FP⟩

attribute [local irreducible] Source.lowerValue Source.objectiveValue IntegralClearedCoefficientBits.Source.value

theorem value_eq (S : Source) (i : ∀ c, Fin (S.free c))
    (objectiveTask gradientTask answer : List Bool → List Bool)
    (ho : ∀ c, answer (objectiveTask c) = S.objectiveValue c)
    (hg : ∀ q, answer (gradientTask q) = (IntegralCriticalGradientBits.family S.toGradient).value q)
    (c : List Bool) : (program S i objectiveTask gradientTask).value answer c = S.lowerValue i c := by
  simp only [SingleCall.Program.value, program, ite_true, pairSnd_pair]
  split_ifs with h
  · rw [ho c]
    exact (by simpa only [h, ite_true] using lower_value S i c)
  · rw [hg]
    exact (by simpa only [h, ite_false] using lower_value S i c)

theorem requests_iff (S : Source) (i : ∀ c, Fin (S.free c))
    (objectiveTask gradientTask answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool) :
    (program S i objectiveTask gradientTask).controller.Requests answer budget c child ↔
      child = if (i c).val = objectiveRank S c then objectiveTask c else gradientTask (lowerGradientQuery S i c) := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, true_and]

end LeanCanny.Algebra.IntegralEulerBits.LowerStage

namespace LeanCanny.Algebra.IntegralEulerLowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralEulerBits
open IntegralBerkowitzBlockBits (original)

noncomputable def program (S : Source) (objectiveTask gradientTask : List Bool → List Bool) : SingleCall.Program :=
  LowerStage.program (S.requery original target (row S) (col S)) (selected S) objectiveTask gradientTask

theorem program_controls (S : Source) (a : Access S) (objectiveTask gradientTask : List Bool → List Bool)
    (ho : objectiveTask ∈ FP) (hg : gradientTask ∈ FP) : (program S objectiveTask gradientTask).Controls :=
  LowerStage.controls _ (a.requery S original target (row S) (col S) IntegralBerkowitzBlockBits.original_FP
    target_binary (row_binary S a) (col_binary S a)) (selected S) (selected_binary S a) _ _ ho hg

theorem program_value (S : Source) (objectiveTask gradientTask answer : List Bool → List Bool)
    (ho : ∀ c, answer (objectiveTask c) = (S.requery original target (row S) (col S)).objectiveValue c)
    (hg : ∀ q, answer (gradientTask q) =
      (IntegralCriticalGradientBits.family (S.requery original target (row S) (col S)).toGradient).value q)
    (q : List Bool) : (program S objectiveTask gradientTask).value answer q = value S q :=
  LowerStage.value_eq (S.requery original target (row S) (col S)) (selected S)
    objectiveTask gradientTask answer ho hg q

end LeanCanny.Algebra.IntegralEulerLowBits
