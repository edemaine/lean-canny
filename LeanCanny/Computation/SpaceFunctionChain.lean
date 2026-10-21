/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Sequential composition by the native tidy machine combinator -/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction
open Complexity Turing.MultiTapeTM

theorem exists_output_length_poly {f : List Bool → List Bool} (E : SpaceFunction f) :
    ∃ p : Polynomial ℕ, ∀ x, (f x).length ≤ p.eval x.length := by
  obtain ⟨c, d, h⟩ := E.computable.polyBounded_length.exists_le
  refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, ?_⟩
  intro x
  simpa only [encBits_apply, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using h x

theorem chain {f g : List Bool → List Bool} (E : SpaceFunction f) (G : SpaceFunction g) :
    SpaceFunction (g ∘ f) := ⟨G.computable.comp E.computable⟩

end LeanCanny.Computation.SpaceFunction
