/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceDeciderFunction

/-! # Branching on a native polynomial-space decision procedure -/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction
open Turing.MultiTapeTM
open scoped Classical

theorem branchDecider {L : Language} {f g : List Bool → List Bool}
    (D : SpaceDecider L) (P : SpaceFunction f) (Q : SpaceFunction g) :
    SpaceFunction (fun x => if x ∈ L then f x else g x) := by
  have h := D.computable.ite P.computable Q.computable
  exact ⟨h.congr fun x => by simp only [decide_eq_true_eq]⟩

end LeanCanny.Computation.SpaceFunction
