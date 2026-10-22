/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.TidyBoundedFold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Binary range products in polynomial space

Only the context and binary index are passed to a factor reader. The fold
stores one accumulator; the caller supplies a bound on every product prefix.
-/

@[expose] public section

namespace LeanCanny.Computation.TidyBoundedFold
open Turing.MultiTapeTM
open scoped BigOperators

variable {α : Type} {eA : α ↪ List Bool}

theorem fold_product (factor : α → ℕ → ℕ) (c : α) (k : ℕ) :
    fold (fun p : α × ℕ × ℕ => p.2.2 * factor p.1 p.2.1) (fun _ => 1) c k =
      ∏ i ∈ Finset.range k, factor c i := by
  induction k with
  | zero => simp only [fold, Finset.range_zero, Finset.prod_empty]
  | succ k ih => simp only [fold, ih, Finset.prod_range_succ]

/-- Read factors in arbitrary polynomial space and multiply them without
materializing the range. Counts are computed in binary, and all accumulator
prefixes must have polynomial encoding length. -/
theorem product_evaluator [Inhabited α] {factor : α → ℕ → ℕ} {count B : α → ℕ}
    (hf : ComputableTidilyInPolySpace (fun p : α × ℕ => factor p.1 p.2)
      (encPair eA encNat) encNat)
    (hn : ComputableTidilyInPolyTime count eA encNat)
    (hB : PolyBounded (fun c => (eA c).length) B)
    (hprefix : ∀ c k, k ≤ count c →
      (encNat (∏ i ∈ Finset.range k, factor c i)).length ≤ B c) :
    ComputableTidilyInPolySpace (fun c => ∏ i ∈ Finset.range (count c), factor c i) eA encNat := by
  have hquery : ComputableTidilyInPolyTime (fun p : α × ℕ × ℕ => (p.1, p.2.1))
      (encPacket eA encNat) (encPair eA encNat) := by fun_prop
  have hacc : ComputableTidilyInPolyTime (fun p : α × ℕ × ℕ => p.2.2)
      (encPacket eA encNat) encNat := by fun_prop
  have hchild : ComputableTidilyInPolySpace
      (fun p : α × ℕ × ℕ => p.2.2 * factor p.1 p.2.1) (encPacket eA encNat) encNat :=
    (ComputableTidilyInPolySpace.of_polyTime ComputableTidilyInPolyTime.binary_mul).comp
      ((ComputableTidilyInPolySpace.of_polyTime hacc).prod (hf.comp (.of_polyTime hquery)))
  have h := evaluator hchild hn (.of_polyTime (ComputableTidilyInPolyTime.const 1)) hB
    (fun c k hk => by rw [fold_product]; exact hprefix c k hk)
  exact h.congr fun c => fold_product factor c _

end LeanCanny.Computation.TidyBoundedFold
