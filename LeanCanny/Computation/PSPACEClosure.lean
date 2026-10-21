/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PSPACERepresentation
public import Complexitylib.Classes.NP.Reduction

/-! # Native PSPACE closure under the existing polynomial-time reductions -/

@[expose] public section

namespace LeanCanny.Computation
open Complexity Turing.MultiTapeTM
open scoped Classical

theorem SpaceDecider.precompose {L : Language} (D : SpaceDecider L)
    (f : List Bool → List Bool) (hf : f ∈ FP) : SpaceDecider (f ⁻¹' L) :=
  SpaceDecider.of_computable
    (D.computable.comp (ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_mem_FP hf)))
    (fun _ => decide_eq_true_iff.symm)

theorem mem_PSPACE_preimage {f : List Bool → List Bool} {L : Language}
    (hf : f ∈ FP) (hL : L ∈ PSPACE) : f ⁻¹' L ∈ PSPACE :=
  ((SpaceDecider.ofPSPACE hL).precompose f hf).mem_PSPACE

theorem mem_PSPACE_of_reduction {L K : Language} (h : L ≤ₚ K) (hK : K ∈ PSPACE) : L ∈ PSPACE := by
  obtain ⟨f, hf, hc⟩ := h
  have heq : L = f ⁻¹' K := by ext x; exact hc x
  rw [heq]
  exact mem_PSPACE_preimage hf hK

end LeanCanny.Computation
