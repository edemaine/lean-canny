/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledIndexedSystem
public import LeanCanny.CountingHierarchy.ControlledFeasibilityFunction

/-! # Boolean functions deciding controlled existential systems -/

public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped Classical

theorem indexedSystem_function_mem {α : Type} {n e k : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P Q : (w : α) → ℕ → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled (fun w => indexedEquationPositivityPolynomial (P w) (Q w) (e w) (k w)) enc a)
    (E : Decoder enc) :
    (fun w => decide (∃ x : Fin (n w) → ℝ,
      (∀ i < e w, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (P w i) = 0) ∧
        ∀ i < k w, 0 < MvPolynomial.eval₂ (Int.castRingHom ℝ) x (Q w i))) ∈
      CountingFunction (a + 25) enc encBool := by
  simpa only [MvPolynomial.eval_map, exists_indexedEquationPositivityPolynomial_zero_iff] using
    C.feasibilityFunction_mem E

end LeanCanny.CountingHierarchy.Controlled
