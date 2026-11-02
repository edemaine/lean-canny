/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.SingleCallController
public import LeanCanny.Computation.SpaceFunctionComposition
/-! # One charged native call to an already verified space subroutine -/
@[expose] public section
namespace LeanCanny.Computation.SingleCall.Program

theorem value_evaluator (P : SingleCall.Program) (h : P.Controls)
    (answer : List Bool→List Bool) (E : SpaceFunction answer) : SpaceFunction (P.value answer) :=
  SpaceFunction.branch P.request h.request (E.call P.query P.finish h.query h.finish) (SpaceFunction.ofFP P.immediate h.immediate)

end LeanCanny.Computation.SingleCall.Program
