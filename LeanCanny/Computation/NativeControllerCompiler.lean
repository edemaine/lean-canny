/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.NativeControllerBranch
public import LeanCanny.Computation.WordResourceEnvelope
/-! # Compiling native branches with arbitrary decreasing task ranks

The rank may include mixed-history routines in addition to arithmetic phases.
Only local native certificates, polynomial word allowances, and a unary rank
are required; the semantic answer is not assumed computable.
-/
@[expose] public section
namespace LeanCanny.Computation.NativeControllerBranch
open Turing.MultiTapeTM

structure FrameBounds where
  root : List Bool → List Bool
  word : List Bool → ℕ
  rank : List Bool → ℕ
  word_unary : UnaryFn word
  rank_unary : UnaryFn rank
  word_eq : ∀ q r, root q = root r → word q = word r

def FrameBounds.Frame (B : FrameBounds) (q child : List Bool) : Prop :=
  B.root child = B.root q ∧ child.length ≤ B.word q ∧ B.rank child < B.rank q

def FrameBounds.Tasks (B : FrameBounds) (r q : List Bool) : Prop :=
  q = r ∨ (B.root q = B.root r ∧ q.length ≤ B.word r)

def FrameBounds.taskBudget (B : FrameBounds) (r : List Bool) : ℕ := r.length + B.word r

theorem FrameBounds.tasks_root (B : FrameBounds) {r q : List Bool} (h : B.Tasks r q) :
    B.root q = B.root r := by
  rcases h with rfl | h
  · rfl
  · exact h.1

theorem FrameBounds.tasks_length (B : FrameBounds) {r q : List Bool} (h : B.Tasks r q) :
    q.length ≤ B.taskBudget r := by
  rcases h with rfl | h
  · exact Nat.le_add_right _ _
  · exact h.2.trans (Nat.le_add_left _ _)

theorem FrameBounds.taskBudget_unary (B : FrameBounds) : UnaryFn B.taskBudget :=
  (UnaryFn.length id_mem_FP).add B.word_unary

theorem evaluator_of_frames (M : Machine) (B : FrameBounds) (answer : List Bool → List Bool)
    (hc : Correct M answer B.Frame) (hs : ∀ q, M.selected q = true)
    (hv : ∀ q, M.model q = answer q)
    (answerBound : List Bool → ℕ) (ha : UnaryFn answerBound)
    (hl : ∀ q, (answer q).length ≤ answerBound q) : SpaceFunction answer := by
  let : Inhabited M.State := ⟨M.defaultValue⟩
  obtain ⟨N, hN, hn⟩ := M.clock_binary.wordEnvelope B.taskBudget_unary
  obtain ⟨R, hR, hr⟩ := B.rank_unary.wordEnvelope B.taskBudget_unary
  obtain ⟨V, hV, hvb⟩ := M.stateBound_unary.wordEnvelope B.taskBudget_unary
  obtain ⟨A, hA, hab⟩ := ha.wordEnvelope B.taskBudget_unary
  let bound := fun r => B.taskBudget r + V r + A r
  have HB : UnaryFn bound := (B.taskBudget_unary.add hV).add hA
  have HBP : PolyBounded (fun q => (encBits q).length) bound := by
    simpa only [encBits_apply, encUnary_apply, List.length_replicate] using HB.polyBounded_length
  refine ⟨M.controller.evaluatorOfOrbits M.certificates answer B.rank M.clock B.Tasks
    N R bound hN hR HBP (fun _ => Or.inl rfl)
    (fun _ q _ => hc.halted q (hs q)) ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro r q hq
    exact hn r q (B.tasks_length hq)
  · intro _ q t _ _ hh
    exact (hc.output q t (hs q) hh).trans (hv q)
  · intro r q t hq ht hh hn'
    obtain ⟨hroot, hword, hdecr⟩ := hc.requests q _ M.clock (hs q) ⟨t, ht, hh, hn', rfl⟩
    exact ⟨Or.inr ⟨hroot.trans (B.tasks_root hq),
      hword.trans_eq (B.word_eq q r (B.tasks_root hq))⟩, hdecr⟩
  · intro r q hq
    exact hr r q (B.tasks_length hq)
  · intro r q hq
    exact (B.tasks_length hq).trans (by dsimp only [bound]; omega)
  · intro r q hq t _
    exact ((hc.state q t (hs q)).trans (hvb r q (B.tasks_length hq))).trans
      (by dsimp only [bound]; omega)
  · intro r q hq
    exact ((hl q).trans (hab r q (B.tasks_length hq))).trans (by dsimp only [bound]; omega)

end LeanCanny.Computation.NativeControllerBranch
