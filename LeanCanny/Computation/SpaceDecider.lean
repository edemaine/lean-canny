/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.HaltingIteration

/-!
# Reusable certified polynomial-space decision procedures

Keeping the executable primitives, first halting time, and resource certificates
together allows another controller to run this procedure as a subroutine. A
PSPACE membership proposition alone does not expose those particular primitives.
The mathematical clock is a proof parameter and is not computed by a transition.
-/

@[expose] public section

namespace LeanCanny.Computation
open Complexity

structure SpaceDecider (L : Language) where
  init : List Bool → List Bool
  advance : List Bool → List Bool
  halt : List Bool → Bool
  answer : List Bool → Bool
  initFP : init ∈ FP
  advanceFP : advance ∈ FP
  haltFP : (fun p => [halt p]) ∈ FP
  answerFP : (fun p => [answer p]) ∈ FP
  space : Polynomial ℕ
  clock : Polynomial ℕ
  time : List Bool → ℕ
  length_le : ∀ x t, t ≤ time x → (advance^[t] (init x)).length ≤ space.eval x.length
  time_le : ∀ x, time x ≤ 2 ^ clock.eval x.length
  before : ∀ x t, t < time x → halt (advance^[t] (init x)) = false
  after : ∀ x, halt (advance^[time x] (init x)) = true
  correct : ∀ x, x ∈ L ↔ answer (advance^[time x] (init x)) = true

theorem SpaceDecider.mem_PSPACE {L : Language} (D : SpaceDecider L) : L ∈ PSPACE :=
  HaltingIteration.mem_PSPACE D.initFP D.advanceFP D.haltFP D.answerFP D.space D.clock D.time
    D.length_le D.time_le D.before D.after D.correct

end LeanCanny.Computation
