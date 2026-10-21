/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SpacePrototype

/-!
# A replacement interface for `BoundedFold.evaluator`

The context and accumulator may use arbitrary fixed binary encodings. The child
receives the context, binary index, and accumulator. A polynomial bound on fold
prefixes suffices; there are no clocks or explicit suspended configurations.
-/

@[expose] public section

namespace LeanCanny.BoundedFoldPrototype

open Turing.MultiTapeTM

variable {α β : Type} {eA : α ↪ List Bool} {eB : β ↪ List Bool}

abbrev encPacket (eA : α ↪ List Bool) (eB : β ↪ List Bool) : α × ℕ × β ↪ List Bool :=
  encPair eA (encPair encNat eB)

def fold (child : α × ℕ × β → β) (seed : α → β) (c : α) : ℕ → β
  | 0 => seed c
  | k + 1 => child (c, k, fold child seed c k)

def step (child : α × ℕ × β → β) (p : α × ℕ × β) : α × ℕ × β :=
  (p.1, p.2.1 + 1, child p)

theorem iterate_step (child : α × ℕ × β → β) (seed : α → β) (c : α) (k : ℕ) :
    (step child)^[k] (c, 0, seed c) = (c, k, fold child seed c k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- A binary-counted fold with a polynomial-space child and short accumulator prefixes. -/
theorem evaluator [Inhabited α] [Inhabited β]
    {child : α × ℕ × β → β} {seed : α → β} {count : α → ℕ} {B : α → ℕ}
    (hc : ComputableTidilyInPolySpace child (encPacket eA eB) eB)
    (hn : ComputableTidilyInPolyTime count eA encNat)
    (hs : ComputableTidilyInPolySpace seed eA eB)
    (hB : PolyBounded (fun c => (eA c).length) B)
    (hstate : ∀ c k, k ≤ count c → (eB (fold child seed c k)).length ≤ B c) :
    ComputableTidilyInPolySpace (fun c => fold child seed c (count c)) eA eB := by
  have hcontext := SpacePrototype.polySpace_of_linear (ComputableTidilyInSpace.fst eA
    (encPair encNat eB))
  have hrest := SpacePrototype.polySpace_of_linear (ComputableTidilyInSpace.snd eA
    (encPair encNat eB))
  have hindex := (SpacePrototype.polySpace_of_linear
    (ComputableTidilyInSpace.fst encNat eB)).comp hrest
  have hsucc := SpacePrototype.polySpace_of_linear
    (ComputableTidilyInSpace.natSucc.weaken ComputableTidilyInSpace.linear_succ)
  have hstep : ComputableTidilyInPolySpace (step child) (encPacket eA eB) (encPacket eA eB) :=
    hcontext.prod ((hsucc.comp hindex).prod hc)
  have hinit : ComputableTidilyInPolySpace (fun c => (c, 0, seed c)) eA (encPacket eA eB) :=
    ComputableTidilyInPolySpace.id'.prod
      ((ComputableTidilyInPolySpace.of_polyTime (ComputableTidilyInPolyTime.const 0)).prod hs)
  have hsize : PolyBounded (fun c => (eA c).length)
      (fun c => 2 * (eA c).length + 2 * (encNat (count c)).length + B c + 2) :=
    ((((PolyBounded.const 2).mul PolyBounded.self).add
      ((PolyBounded.const 2).mul hn.polyBounded_length)).add hB).add (PolyBounded.const 2)
  have hit := ComputableTidilyInPolySpace.iterate hn hinit hstep hsize (fun c k hk => by
    rw [iterate_step]
    have hi := ComputableTidilyInO.length_encNat_mono hk
    have hv := hstate c k hk
    simp only [encPacket, length_encPair]
    omega)
  have hout := (SpacePrototype.polySpace_of_linear (ComputableTidilyInSpace.snd encNat eB)).comp
    ((SpacePrototype.polySpace_of_linear (ComputableTidilyInSpace.snd eA
      (encPair encNat eB))).comp hit)
  exact hout.congr fun c => by rw [iterate_step]

end LeanCanny.BoundedFoldPrototype
