/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalHistoryEvaluator
public import LeanCanny.Computation.WordResourceEnvelope

/-! # Global stack bounds from native local critical-stage bounds

Native binary local clocks and unary local state allowances give common
bounds for all flat descendants, because their words have one polynomial
allowance. No stage-specific monotonicity argument for its clock or state
formula is needed. The initial input may contain arbitrary stale padding.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalHistoryEvaluator
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

theorem evaluator_of_local_bounds {S : Type} [Inhabited S] {encS : S ↪ List Bool}
    (F : Parameters) (a : Access F) (C : RecursiveController.Controller (List Bool) S)
    (hC : C.Certificates (encQ := encBits) (encS := encS))
    (x : (q : List Bool) → ZMod (IntegralCriticalHistoryTask.modulus F q))
    (budget localBound : List Bool → ℕ) (hbudget : BinaryFn budget) (hlocal : UnaryFn localBound)
    (hstop : ∀ q, C.halted ((C.reference (fun q => residueBits (x q)))^[budget q] (C.initial q)) = true)
    (hdone : ∀ q t, t ≤ budget q →
      C.halted ((C.reference (fun q => residueBits (x q)))^[t] (C.initial q)) = true →
      C.output ((C.reference (fun q => residueBits (x q)))^[t] (C.initial q)) = residueBits (x q))
    (hchild : ∀ q child, C.Requests (fun q => residueBits (x q)) budget q child →
      RankedHistoryTask.root child = RankedHistoryTask.root q ∧ child.length ≤ wordBudget F q ∧ rank F child < rank F q)
    (hstate : ∀ q t, t ≤ budget q →
      (encS ((C.reference (fun q => residueBits (x q)))^[t] (C.initial q))).length ≤ localBound q) :
    SpaceFunction (fun q => residueBits (x q)) := by
  obtain ⟨N, hN, hn⟩ := hbudget.wordEnvelope (taskBudget_unary F a)
  obtain ⟨V, hV, hv⟩ := hlocal.wordEnvelope (taskBudget_unary F a)
  let B := fun r => taskBudget F r + V r + residueWidth F r
  have HB : UnaryFn B := ((taskBudget_unary F a).add hV).add (residueWidth_unary F a)
  have HBP : PolyBounded (fun q => (encBits q).length) B := by
    simpa only [encBits_apply, encUnary_apply, List.length_replicate] using HB.polyBounded_length
  refine ⟨C.evaluatorOfOrbits hC (fun q => residueBits (x q)) (rank F) budget (Tasks F)
    N (rankBudget F) B hN (rankBudget_unary F a) HBP (tasks_self F)
    (fun _ q _ => hstop q) ?_ (fun _ q t _ ht hh => hdone q t ht hh) ?_ ?_ ?_ ?_ ?_⟩
  · intro r q hq
    exact hn r q (tasks_length F hq)
  · intro r q t hq ht hh hh'
    obtain ⟨hr, hl, hd⟩ := hchild q _ ⟨t, ht, hh, hh', rfl⟩
    exact ⟨Or.inr ⟨hr.trans (tasks_root F hq), hl.trans_eq (wordBudget_eq F (tasks_root F hq))⟩, hd⟩
  · intro r q hq
    exact (tasks_rank F hq).le
  · intro r q hq
    exact (tasks_length F hq).trans (by dsimp only [B]; omega)
  · intro r q hq t ht
    have H := (hstate q t ht).trans (hv r q (tasks_length F hq))
    dsimp only [B]
    omega
  · intro r q hq
    have H := answer_length F x q
    have HE : residueWidth F q = residueWidth F r := by
      unfold residueWidth
      rw [tasks_root F hq]
    rw [HE] at H
    exact H.trans (by dsimp only [B]; omega)

end LeanCanny.Algebra.IntegralCriticalHistoryEvaluator
