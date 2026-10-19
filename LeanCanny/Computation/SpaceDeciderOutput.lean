/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunction

/-! # Using a certified decision procedure as an output subroutine -/

@[expose] public section

namespace LeanCanny.Computation.SpaceDecider
open Complexity

noncomputable def indicator {L : Language} (D : SpaceDecider L) :
    SpaceFunction (fun x => [@decide (x ∈ L) (Classical.propDecidable _)]) := by
  classical
  refine {
    init := D.init
    advance := D.advance
    halt := D.halt
    output := fun p => [D.answer p]
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
    correct := ?_ }
  intro x
  apply congrArg (fun b : Bool => [b])
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact (D.correct x).symm

end LeanCanny.Computation.SpaceDecider
