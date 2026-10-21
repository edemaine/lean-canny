/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunction

/-! # Input preparation and pairing by tidy space composition -/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction
open Complexity Turing.MultiTapeTM

theorem congr {f g : List Bool → List Bool} (E : SpaceFunction f) (h : f = g) : SpaceFunction g := h ▸ E

theorem precompose {f : List Bool → List Bool} (E : SpaceFunction f)
    (g : List Bool → List Bool) (hg : g ∈ FP) : SpaceFunction (f ∘ g) :=
  ⟨E.computable.comp (ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_mem_FP hg))⟩

theorem pairOutputs {f g : List Bool → List Bool} (E : SpaceFunction f) (G : SpaceFunction g) :
    SpaceFunction (fun x => Complexity.pair (f x) (g x)) :=
  ⟨(ComputableTidilyInPolySpace.of_polyTime
    (TidyFP.pair (ComputableTidilyInPolyTime.fst encBits encBits)
      (ComputableTidilyInPolyTime.snd encBits encBits))).comp
        (E.computable.prod G.computable)⟩

theorem withInput {f : List Bool → List Bool} (E : SpaceFunction f) :
    SpaceFunction (fun x => Complexity.pair x (f x)) :=
  pairOutputs ⟨ComputableTidilyInPolySpace.id'⟩ E

end LeanCanny.Computation.SpaceFunction
