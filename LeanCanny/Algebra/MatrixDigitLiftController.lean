/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixDigitLiftSpace
public import LeanCanny.Computation.ControllerRequests

/-! # Resumable routing through retained scalar basis digits

Matching low digits request one old matrix entry at quotient indices.
Mismatching digits return zero immediately. The controller uses no native
certificate for the old matrix reader.
-/

@[expose] public section
namespace LeanCanny.Algebra.MatrixDigitLiftBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def program (F : Family) (task : List Bool → List Bool) : SingleCall.Program where
  request c := decide ((F.row c).modNat = (F.col c).modNat)
  query c := task (query F c)
  immediate _ := []
  finish := pairSnd

theorem program_controls (F : Family) (a : Access F) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (program F task).Controls where
  request := (guard_FP F a).flag_mem_FP
  query := mem_FP_comp (f := query F) (g := task) (query_FP F a) ht
  immediate := constFn_mem_FP []
  finish := pairSnd_mem_FP

theorem program_value (F : Family) (task answer : List Bool → List Bool)
    (ha : ∀ c, (F.row c).modNat = (F.col c).modNat →
      answer (task (query F c)) = residueBits (F.matrix c (F.row c).divNat (F.col c).divNat)) (c : List Bool) :
    (program F task).value answer c = F.value c := by
  by_cases h : (F.row c).modNat = (F.col c).modNat
  · simp only [SingleCall.Program.value, program, h, decide_true, ite_true, pairSnd_pair, Family.value, ha c h]
  · simp only [SingleCall.Program.value, program, h, decide_false, Bool.false_eq_true, ite_false, Family.value]
    exact ArithmeticBits.zero_residueBits _

theorem program_requests_iff (F : Family) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (c child : List Bool) :
    (program F task).controller.Requests answer budget c child ↔
      (F.row c).modNat = (F.col c).modNat ∧ child = task (query F c) := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

end LeanCanny.Algebra.MatrixDigitLiftBits
