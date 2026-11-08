/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.NativeSpaceClosure

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Fold

/-! # Binary-counted folds through the native plain space calculus

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
    (h : ComputableInSpace f eC eD fun c => (eC c).length) :
    ComputableInPolySpace f eC eD :=
  ComputableInPolySpace.of_inSpace PolyBounded.self h

private theorem fold_eq_natFold (child : α × ℕ × β → β) (seed : α → β) (c : α) (k : ℕ) :
    fold child seed c k = k.fold (fun i _ a => child (c, i, a)) (seed c) := by
  induction k with
  | zero => simp only [fold, Nat.fold_zero]
  | succ k ih => rw [fold, Nat.fold_succ, ih]

theorem evaluator [Inhabited α] [Inhabited β]
    {child : α × ℕ × β → β} {seed : α → β} {count : α → ℕ} {B : α → ℕ}
    (hc : ComputableInPolySpace child (encPacket eA eB) eB)
    (hn : ComputableTidilyInPolyTime count eA encNat)
    (hs : ComputableInPolySpace seed eA eB)
    (hB : PolyBounded (fun c => (eA c).length) B)
    (hstate : ∀ c k, k ≤ count c → (eB (fold child seed c k)).length ≤ B c) :
    ComputableInPolySpace (fun c => fold child seed c (count c)) eA eB := by
  have h := ComputableInPolySpace.natFold (step := fun c i a => child (c, i, a))
    hn.computableInPolyTime hs hc hB (fun c k hk => by
      rw [← fold_eq_natFold]
      exact hstate c k hk)
  exact h.congr fun c => (fold_eq_natFold child seed c (count c)).symm

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
    (hc : ComputableInPolySpace child (encPacket eA eB) eB)
    (hn : ComputableTidilyInPolyTime count eA encNat)
    (hs : ComputableInPolySpace seed eA eB)
    (v : α → ℕ → β) (hseed : ∀ c, seed c = v c 0)
    (hstep : ∀ c k, k < count c → child (c, k, v c k) = v c (k + 1))
    (hB : PolyBounded (fun c => (eA c).length) B)
    (hstate : ∀ c k, k ≤ count c → (eB (v c k)).length ≤ B c) :
    ComputableInPolySpace (fun c => v c (count c)) eA eB := by
  have h := evaluator hc hn hs hB (fun c k hk => by
    rw [fold_spec v hseed hstep c k hk]
    exact hstate c k hk)
  exact h.congr fun c => fold_spec v hseed hstep c _ le_rfl

end LeanCanny.Computation.TidyBoundedFold
