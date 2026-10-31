/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralReductionActionSpace
public import LeanCanny.Algebra.IntegralBlockPowerRecursiveStage
public import LeanCanny.Computation.ControllerRequests

/-! # Resumable shifted reduction-action entries

Nonnormal columns return zero locally. Normal columns request one entry
of the actual algebra-valued reduction power. The separate binary outer
and old basis indices are exactly those of the existing action source.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralReductionActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def program (S : Source) (task : List Bool → List Bool) : SingleCall.Program where
  request p := decide (normalGuard S p)
  query := task
  immediate _ := []
  finish := pairSnd

theorem program_controls (S : Source) (h : Controls S) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (program S task).Controls := ⟨h.normal.flag_mem_FP, ht, constFn_mem_FP [], pairSnd_mem_FP⟩

theorem program_value (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ p, normalGuard S p → answer (task p) = (powerFamily S).value p) (p : List Bool) :
    (program S task).value answer p = entryProgram S p := by
  by_cases h : normalGuard S p
  · simp only [SingleCall.Program.value, program, h, decide_true, ite_true, pairSnd_pair, entryProgram, he p h]
  · simp only [SingleCall.Program.value, program, h, decide_false, Bool.false_eq_true, ite_false, entryProgram]

theorem program_packet (S : Source) (task answer : List Bool → List Bool)
    (he : ∀ p, normalGuard S p → answer (task p) = (powerFamily S).value p)
    (c : List Bool) (i j : Fin (S.dimension c)) (r t : Fin (S.rank c)) :
    (program S task).value answer (packet c i.val j.val r.val t.val) =
      residueBits (((actionSource S).entryMatrix c i j r t : ℤ) : ZMod (S.modulus c)) :=
  (program_value S task answer he _).trans (entry_correct S c i j r t)

theorem program_requests_iff (S : Source) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (p q : List Bool) :
    (program S task).controller.Requests answer budget p q ↔ normalGuard S p ∧ q = task p := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

end LeanCanny.Algebra.IntegralReductionActionBits
