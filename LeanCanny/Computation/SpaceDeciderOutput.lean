/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceDeciderFunction

/-! # A decision flag as a tidy output subroutine -/

@[expose] public section

namespace LeanCanny.Computation.SpaceDecider
open Complexity

theorem indicator {L : Language} (D : SpaceDecider L) :
    SpaceFunction (fun x => [@decide (x ∈ L) (Classical.propDecidable _)]) :=
  D.flagEvaluator

end LeanCanny.Computation.SpaceDecider
