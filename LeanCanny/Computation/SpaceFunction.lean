/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceDecider

/-!
# Certified polynomial-space output routines

The transition and output projection are FP, while the complete computation may
take exponentially many transitions. The first halting time, state-length bound,
and output correctness make the routine usable as a suspended child. This is an
explicit evaluator certificate, rather than a new complexity-class definition.
-/

@[expose] public section

namespace LeanCanny.Computation
open Complexity

structure SpaceFunction (f : List Bool → List Bool) where
  init : List Bool → List Bool
  advance : List Bool → List Bool
  halt : List Bool → Bool
  output : List Bool → List Bool
  initFP : init ∈ FP
  advanceFP : advance ∈ FP
  haltFP : (fun p => [halt p]) ∈ FP
  outputFP : output ∈ FP
  space : Polynomial ℕ
  clock : Polynomial ℕ
  time : List Bool → ℕ
  length_le : ∀ x t, t ≤ time x → (advance^[t] (init x)).length ≤ space.eval x.length
  time_le : ∀ x, time x ≤ 2 ^ clock.eval x.length
  before : ∀ x t, t < time x → halt (advance^[t] (init x)) = false
  after : ∀ x, halt (advance^[time x] (init x)) = true
  correct : ∀ x, output (advance^[time x] (init x)) = f x

def SpaceFunction.decider {f : List Bool → List Bool} (E : SpaceFunction f)
    {L : Language} (accept : List Bool → Bool) (ha : (fun y => [accept y]) ∈ FP)
    (hc : ∀ x, x ∈ L ↔ accept (f x) = true) : SpaceDecider L where
  init := E.init
  advance := E.advance
  halt := E.halt
  answer := fun p => accept (E.output p)
  initFP := E.initFP
  advanceFP := E.advanceFP
  haltFP := E.haltFP
  answerFP := mem_FP_comp E.outputFP ha
  space := E.space
  clock := E.clock
  time := E.time
  length_le := E.length_le
  time_le := E.time_le
  before := E.before
  after := E.after
  correct := fun x => by rw [E.correct x]; exact hc x

def SpaceFunction.postcompose {f : List Bool → List Bool} (E : SpaceFunction f)
    (g : List Bool → List Bool) (hg : g ∈ FP) : SpaceFunction (g ∘ f) where
  init := E.init
  advance := E.advance
  halt := E.halt
  output := g ∘ E.output
  initFP := E.initFP
  advanceFP := E.advanceFP
  haltFP := E.haltFP
  outputFP := mem_FP_comp E.outputFP hg
  space := E.space
  clock := E.clock
  time := E.time
  length_le := E.length_le
  time_le := E.time_le
  before := E.before
  after := E.after
  correct := fun x => congrArg g (E.correct x)

end LeanCanny.Computation
