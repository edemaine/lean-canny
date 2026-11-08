/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunction

/-! # Input preparation and pairing by plain space composition -/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolySpace

-- Composed projections fix the intermediate encoding before native proof search.
@[fun_prop]
theorem fst' {α β γ : Type} {enc : α ↪ List Bool}
    {eA : β ↪ List Bool} {eB : γ ↪ List Bool} {f : α → β × γ}
    (hf : ComputableInPolySpace f enc (encPair eA eB)) :
    ComputableInPolySpace (fun x => (f x).1) enc eA :=
  (of_tidyPolyTime (ComputableTidilyInPolyTime.fst eA eB)).comp hf

@[fun_prop]
theorem snd' {α β γ : Type} {enc : α ↪ List Bool}
    {eA : β ↪ List Bool} {eB : γ ↪ List Bool} {f : α → β × γ}
    (hf : ComputableInPolySpace f enc (encPair eA eB)) :
    ComputableInPolySpace (fun x => (f x).2) enc eB :=
  (of_tidyPolyTime (ComputableTidilyInPolyTime.snd eA eB)).comp hf

@[fun_prop]
theorem const {α β : Type} (enc : α ↪ List Bool) (eB : β ↪ List Bool) (b : β) :
    ComputableInPolySpace (fun _ : α => b) enc eB :=
  of_tidyPolyTime (ComputableTidilyInPolyTime.const b)

end Turing.MultiTapeTM.ComputableInPolySpace

namespace LeanCanny.Computation
open Turing.MultiTapeTM

/-- Compose arbitrary space-bounded readers with the project's raw pair codec. -/
@[fun_prop]
theorem rawPair_computable {α : Type} {enc : α ↪ List Bool} {f g : α → List Bool}
    (hf : ComputableInPolySpace f enc encBits)
    (hg : ComputableInPolySpace g enc encBits) :
    ComputableInPolySpace (fun x => LeanCanny.pair (f x) (g x)) enc encBits :=
  (ComputableInPolySpace.of_tidyPolyTime
    (pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
      (ComputableTidilyInPolyTime.snd encBits encBits))).comp (hf.prod hg)

namespace SpaceFunction

theorem congr {f g : List Bool → List Bool} (E : SpaceFunction f) (h : f = g) : SpaceFunction g := h ▸ E

theorem precompose {f : List Bool → List Bool} (E : SpaceFunction f)
    (g : List Bool → List Bool) (hg : g ∈ FP) : SpaceFunction (f ∘ g) :=
  ⟨E.computable.comp (ComputableInPolySpace.of_tidyPolyTime (FP.computable hg))⟩

theorem pairOutputs {f g : List Bool → List Bool} (E : SpaceFunction f) (G : SpaceFunction g) :
    SpaceFunction (fun x => LeanCanny.pair (f x) (g x)) :=
  ⟨rawPair_computable E.computable G.computable⟩

theorem withInput {f : List Bool → List Bool} (E : SpaceFunction f) :
    SpaceFunction (fun x => LeanCanny.pair x (f x)) :=
  pairOutputs ⟨ComputableInPolySpace.id'⟩ E

/-- Prepare a child query, retain its input, and finish with the child result.
All three raw functions retain their behavior on malformed packets. -/
theorem call {f : List Bool → List Bool} (E : SpaceFunction f)
    (query finish : List Bool → List Bool) (hq : query ∈ FP) (hf : finish ∈ FP) :
    SpaceFunction (fun x => finish (LeanCanny.pair x (f (query x)))) := by
  exact ((E.precompose query hq).withInput.postcompose finish hf).congr (funext fun _ => rfl)

end SpaceFunction
end LeanCanny.Computation
