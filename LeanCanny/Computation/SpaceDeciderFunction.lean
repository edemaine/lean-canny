/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunction

/-! # Predicate flags from certified space deciders -/

@[expose] public section

namespace LeanCanny.Computation
open Complexity
open scoped Classical

def SpaceDecider.congr {L M : Language} (D : SpaceDecider L) (h : L = M) : SpaceDecider M := h ▸ D

noncomputable def SpaceDecider.flagEvaluator {L : Language} (D : SpaceDecider L) :
    SpaceFunction (fun x => [decide (x ∈ L)]) where
  init := D.init
  advance := D.advance
  halt := D.halt
  output p := [D.answer p]
  initFP := D.initFP
  advanceFP := D.advanceFP
  haltFP := D.haltFP
  outputFP := D.answerFP
  space := D.space
  clock := D.clock
  time := D.time
  length_le := D.length_le
  time_le := D.time_le
  before := D.before
  after := D.after
  correct x := by
    by_cases hx : x ∈ L
    · simp only [D.correct x |>.mp hx, hx, decide_true]
    · have hb : D.answer (D.advance^[D.time x] (D.init x)) = false :=
        Bool.eq_false_iff.mpr (fun h => hx ((D.correct x).mpr h))
      simp only [hb, hx, decide_false]

end LeanCanny.Computation
