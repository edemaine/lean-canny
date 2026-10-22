/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionBranch
public import LeanCanny.Computation.PolynomialBounds

/-! # Sequential composition by the native tidy machine combinator -/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction
open Turing.MultiTapeTM

theorem exists_output_length_poly {f : List Bool → List Bool} (E : SpaceFunction f) :
    ∃ p : Polynomial ℕ, ∀ x, (f x).length ≤ p.eval x.length := by
  simpa only [encBits_apply] using E.computable.polyBounded_length.exists_polynomial

theorem chain {f g : List Bool → List Bool} (E : SpaceFunction f) (G : SpaceFunction g) :
    SpaceFunction (g ∘ f) := ⟨G.computable.comp E.computable⟩

end LeanCanny.Computation.SpaceFunction
