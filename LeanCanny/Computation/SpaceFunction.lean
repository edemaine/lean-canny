/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceDecider

/-! # Compositional polynomial-space output certificates

This proof-only interface contains exactly Complexitylib's plain space
certificate. Composition and iteration use the library's machine combinators.
-/

@[expose] public section

namespace LeanCanny.Computation
open Turing.MultiTapeTM

structure SpaceFunction (f : List Bool → List Bool) : Prop where
  computable : ComputableInPolySpace f encBits encBits

theorem SpaceFunction.decider {f : List Bool → List Bool} (E : SpaceFunction f)
    {L : Language} (accept : List Bool → Bool) (ha : (fun y => [accept y]) ∈ FP)
    (hc : ∀ x, x ∈ L ↔ accept (f x) = true) : SpaceDecider L :=
  SpaceDecider.of_computable
    ((ComputableInPolySpace.of_tidyPolyTime (flag_computable ha)).comp E.computable) hc

theorem SpaceFunction.postcompose {f : List Bool → List Bool} (E : SpaceFunction f)
    (g : List Bool → List Bool) (hg : g ∈ FP) : SpaceFunction (g ∘ f) :=
  ⟨(ComputableInPolySpace.of_tidyPolyTime (FP.computable hg)).comp E.computable⟩

end LeanCanny.Computation
