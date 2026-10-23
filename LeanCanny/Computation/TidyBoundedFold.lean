/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace

/-! # Binary-counted folds in the tidy space calculus

The child receives the context, binary index, and accumulator. Its computation
may take arbitrary time. A polynomial bound on accumulator prefixes suffices.
-/

@[expose] public section

namespace LeanCanny.Computation.TidyBoundedFold

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

theorem of_linear {γ δ : Type} {eC : γ ↪ List Bool} {eD : δ ↪ List Bool} {f : γ → δ}
    (h : ComputableTidilyInSpace f eC eD fun c => (eC c).length) :
    ComputableTidilyInPolySpace f eC eD := by
  obtain ⟨T, h⟩ := h
  exact ⟨T, _, PolyBounded.self, h⟩

theorem evaluator [Inhabited α] [Inhabited β]
    {child : α × ℕ × β → β} {seed : α → β} {count : α → ℕ} {B : α → ℕ}
    (hc : ComputableTidilyInPolySpace child (encPacket eA eB) eB)
    (hn : ComputableTidilyInPolyTime count eA encNat)
    (hs : ComputableTidilyInPolySpace seed eA eB)
    (hB : PolyBounded (fun c => (eA c).length) B)
    (hstate : ∀ c k, k ≤ count c → (eB (fold child seed c k)).length ≤ B c) :
    ComputableTidilyInPolySpace (fun c => fold child seed c (count c)) eA eB := by
  have hcontext := of_linear (ComputableTidilyInSpace.fst eA (encPair encNat eB))
  have hrest := of_linear (ComputableTidilyInSpace.snd eA (encPair encNat eB))
  have hindex := (of_linear (ComputableTidilyInSpace.fst encNat eB)).comp hrest
  have hsucc := of_linear
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
  have hout := (of_linear (ComputableTidilyInSpace.snd encNat eB)).comp
    ((of_linear (ComputableTidilyInSpace.snd eA (encPair encNat eB))).comp hit)
  exact hout.congr fun c => by rw [iterate_step]

/-- Semantic correctness of every prefix up to and including the final state. -/
theorem fold_spec {child : α × ℕ × β → β} {seed : α → β} {count : α → ℕ}
    (v : α → ℕ → β) (hseed : ∀ c, seed c = v c 0)
    (hstep : ∀ c k, k < count c → child (c, k, v c k) = v c (k + 1))
    (c : α) (k : ℕ) (hk : k ≤ count c) : fold child seed c k = v c k := by
  induction k with
  | zero => exact hseed c
  | succ k ih => rw [fold, ih (by omega), hstep c k (by omega)]

/-- Evaluate a semantic prefix sequence using a bound in the original input.
The bound includes prefix zero and the final prefix. -/
theorem evaluator_spec [Inhabited α] [Inhabited β]
    {child : α × ℕ × β → β} {seed : α → β} {count : α → ℕ} {B : α → ℕ}
    (hc : ComputableTidilyInPolySpace child (encPacket eA eB) eB)
    (hn : ComputableTidilyInPolyTime count eA encNat)
    (hs : ComputableTidilyInPolySpace seed eA eB)
    (v : α → ℕ → β) (hseed : ∀ c, seed c = v c 0)
    (hstep : ∀ c k, k < count c → child (c, k, v c k) = v c (k + 1))
    (hB : PolyBounded (fun c => (eA c).length) B)
    (hstate : ∀ c k, k ≤ count c → (eB (v c k)).length ≤ B c) :
    ComputableTidilyInPolySpace (fun c => v c (count c)) eA eB := by
  have h := evaluator hc hn hs hB (fun c k hk => by
    rw [fold_spec v hseed hstep c k hk]
    exact hstate c k hk)
  exact h.congr fun c => fold_spec v hseed hstep c _ le_rfl

end LeanCanny.Computation.TidyBoundedFold
