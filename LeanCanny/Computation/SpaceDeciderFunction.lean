/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunction

/-! # Predicate flags from native PSPACE certificates -/

@[expose] public section

namespace LeanCanny.Computation
open Complexity Turing.MultiTapeTM
open scoped Classical

theorem SpaceDecider.flagEvaluator {L : Language} (D : SpaceDecider L) :
    SpaceFunction (fun x => [decide (x ∈ L)]) := by
  obtain ⟨T, S, hS, h⟩ := D.computable
  exact ⟨T, S, hS, h.of_enc_eq fun _ => rfl⟩

end LeanCanny.Computation
