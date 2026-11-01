/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalLocalBounds
public import LeanCanny.Computation.ControllerRequests

/-! # Native ranked evaluation for one-request critical controllers

The local clock is one. The stored answer is charged by the original root's
modulus cap. Only the guarded query needs the root, rank, and word contracts;
malformed inputs and unused queries impose no additional requirements.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalHistoryEvaluator
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

theorem evaluator_of_singleCall_certificates (F : Parameters) (a : Access F) (P : SingleCall.Program) (hP : P.controller.Certificates (encQ := encBits) (encS := SingleCall.encState))
    (x : (q : List Bool) → ZMod (IntegralCriticalHistoryTask.modulus F q))
    (hvalue : ∀ q, P.value (fun q => residueBits (x q)) q = residueBits (x q))
    (hquery : ∀ q, P.request q = true → RankedHistoryTask.root (P.query q) = RankedHistoryTask.root q ∧
      (P.query q).length ≤ wordBudget F q ∧ rank F (P.query q) < rank F q) :
    SpaceFunction (fun q => residueBits (x q)) := by
  let B := fun q : List Bool => 2 * q.length + 4 + residueWidth F q
  have HB : UnaryFn B :=
    (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 4)).add (residueWidth_unary F a)
  apply evaluator_of_local_bounds F a P.controller hP x (fun _ => 1) B (BinaryFn.const 1) HB
  · intro q
    exact P.halted_after _ q
  · intro q t _ hh
    exact (P.output_when_halted _ q t hh).trans (hvalue q)
  · intro q child hc
    obtain ⟨hr, rfl⟩ := (P.requests_iff _ _ q child).mp hc
    exact hquery q hr
  · intro q t _
    apply P.state_length_of_bound
    intro hr
    have H := answer_length F x (P.query q)
    have HE : residueWidth F (P.query q) = residueWidth F q := by
      unfold residueWidth
      rw [(hquery q hr).1]
    exact H.trans_eq HE

theorem evaluator_of_singleCall (F : Parameters) (a : Access F) (P : SingleCall.Program) (hP : P.Controls)
    (x : (q : List Bool) → ZMod (IntegralCriticalHistoryTask.modulus F q))
    (hvalue : ∀ q, P.value (fun q => residueBits (x q)) q = residueBits (x q))
    (hquery : ∀ q, P.request q = true → RankedHistoryTask.root (P.query q) = RankedHistoryTask.root q ∧
      (P.query q).length ≤ wordBudget F q ∧ rank F (P.query q) < rank F q) :
    SpaceFunction (fun q => residueBits (x q)) :=
  evaluator_of_singleCall_certificates F a P (P.certificates hP) x hvalue hquery

end LeanCanny.Algebra.IntegralCriticalHistoryEvaluator
