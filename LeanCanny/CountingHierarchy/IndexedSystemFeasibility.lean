/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledIndexedSystem
public import LeanCanny.CountingHierarchy.ControlledFeasibility

/-! # A counting-level decision for equations and strict positivity -/

public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

/-- The constructed one-polynomial system can be passed directly to the general
feasibility decision. The number of auxiliary variables is its unary positivity count. -/
theorem indexedSystem_feasibility_mem {α : Type} {n e k : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P Q : (w : α) → ℕ → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled (fun w => indexedEquationPositivityPolynomial (P w) (Q w) (e w) (k w)) enc a)
    (E : Decoder enc) :
    {w | ∃ x : Fin (n w) → ℝ,
      (∀ i < e w, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (P w i) = 0) ∧
        ∀ i < k w, 0 < MvPolynomial.eval₂ (Int.castRingHom ℝ) x (Q w i)} ∈
      CountingLevel (a + 26) enc := by
  have h := C.feasibility_mem E
  convert h using 1
  ext w
  simp only [Set.mem_ofPred_eq, MvPolynomial.eval_map]
  exact (exists_indexedEquationPositivityPolynomial_zero_iff (P w) (Q w) (e w) (k w)).symm

end LeanCanny.CountingHierarchy.Controlled
