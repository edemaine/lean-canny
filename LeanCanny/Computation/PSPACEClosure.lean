/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PSPACERepresentation
public import Complexitylib.Classes.NP.Reduction

/-!
# PSPACE closure under polynomial-time preprocessing and reductions

Preprocessing composes a decider's resource polynomials with an FP output
length bound. The representation theorem makes this construction available
for every Complexitylib PSPACE language, not just already packaged deciders.
-/

@[expose] public section

namespace LeanCanny.Computation
open Complexity

noncomputable def SpaceDecider.precompose {L : Language} (D : SpaceDecider L)
    (f : List Bool → List Bool) (hf : f ∈ FP) : SpaceDecider (f ⁻¹' L) := by
  let p := Classical.choose (Cobham.output_length_poly_of_mem_FP hf)
  have hp : ∀ x, (f x).length ≤ p.eval x.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hf)
  refine {
    init := D.init ∘ f
    advance := D.advance
    halt := D.halt
    answer := D.answer
    initFP := mem_FP_comp hf D.initFP
    advanceFP := D.advanceFP
    haltFP := D.haltFP
    answerFP := D.answerFP
    space := D.space.comp p
    clock := D.clock.comp p
    time := D.time ∘ f
    length_le := ?_
    time_le := ?_
    before := fun x => D.before (f x)
    after := fun x => D.after (f x)
    correct := fun x => D.correct (f x) }
  · intro x t ht
    have h := (D.length_le (f x) t ht).trans (polynomial_eval_mono_nat D.space (hp x))
    simpa only [Polynomial.eval_comp, Function.comp_apply] using h
  · intro x
    have h := (D.time_le (f x)).trans
      (Nat.pow_le_pow_right (by decide) (polynomial_eval_mono_nat D.clock (hp x)))
    simpa only [Polynomial.eval_comp, Function.comp_apply] using h

theorem mem_PSPACE_preimage {f : List Bool → List Bool} {L : Language}
    (hf : f ∈ FP) (hL : L ∈ PSPACE) : f ⁻¹' L ∈ PSPACE :=
  ((SpaceDecider.ofPSPACE hL).precompose f hf).mem_PSPACE

theorem mem_PSPACE_of_reduction {L K : Language} (h : L ≤ₚ K) (hK : K ∈ PSPACE) : L ∈ PSPACE := by
  obtain ⟨f, hf, hc⟩ := h
  have heq : L = f ⁻¹' K := by ext x; exact hc x
  rw [heq]
  exact mem_PSPACE_preimage hf hK

end LeanCanny.Computation
