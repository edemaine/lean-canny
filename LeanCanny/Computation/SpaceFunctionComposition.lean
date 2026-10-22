/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunction

/-! # Input preparation and pairing by tidy space composition -/

@[expose] public section

namespace LeanCanny.Computation
open Turing.MultiTapeTM

/-- Compose arbitrary space-bounded readers with the project's raw pair codec. -/
@[fun_prop]
theorem rawPair_computable {α : Type} {enc : α ↪ List Bool} {f g : α → List Bool}
    (hf : ComputableTidilyInPolySpace f enc encBits)
    (hg : ComputableTidilyInPolySpace g enc encBits) :
    ComputableTidilyInPolySpace (fun x => LeanCanny.pair (f x) (g x)) enc encBits :=
  (ComputableTidilyInPolySpace.of_polyTime
    (pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
      (ComputableTidilyInPolyTime.snd encBits encBits))).comp (hf.prod hg)

namespace SpaceFunction

theorem congr {f g : List Bool → List Bool} (E : SpaceFunction f) (h : f = g) : SpaceFunction g := h ▸ E

theorem precompose {f : List Bool → List Bool} (E : SpaceFunction f)
    (g : List Bool → List Bool) (hg : g ∈ FP) : SpaceFunction (f ∘ g) :=
  ⟨E.computable.comp (ComputableTidilyInPolySpace.of_polyTime (FP.computable hg))⟩

theorem pairOutputs {f g : List Bool → List Bool} (E : SpaceFunction f) (G : SpaceFunction g) :
    SpaceFunction (fun x => LeanCanny.pair (f x) (g x)) :=
  ⟨rawPair_computable E.computable G.computable⟩

theorem withInput {f : List Bool → List Bool} (E : SpaceFunction f) :
    SpaceFunction (fun x => LeanCanny.pair x (f x)) :=
  pairOutputs ⟨ComputableTidilyInPolySpace.id'⟩ E

end SpaceFunction
end LeanCanny.Computation
