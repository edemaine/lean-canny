/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.EquationPositivityPolynomial
public import LeanCanny.CountingHierarchy.ControlledOptionalCoordinate

/-! # Indexed equations and positivity tests with a uniform auxiliary block -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped BigOperators Classical

variable {n : ℕ}

noncomputable def indexedEquationPositivityPolynomial
    (P Q : ℕ → MvPolynomial (Fin n) ℤ) (e k : ℕ) : MvPolynomial (Fin (n + k)) ℤ :=
  (∑ i ∈ Finset.range e, MvPolynomial.rename (Fin.castAdd k) (P i) ^ 2) +
    ∑ i ∈ Finset.range k, (MvPolynomial.rename (Fin.castAdd k) (Q i) *
      optionalCoordinate (n + k) (n + i) ^ 2 - 1) ^ 2

theorem indexedEquationPositivityPolynomial_eq
    (P Q : ℕ → MvPolynomial (Fin n) ℤ) (e k : ℕ) :
    indexedEquationPositivityPolynomial P Q e k =
      equationPositivityPolynomial (fun i : Fin e => P i.val) (fun i : Fin k => Q i.val) := by
  rw [indexedEquationPositivityPolynomial, equationPositivityPolynomial]
  congr 1
  · exact (Fin.sum_univ_eq_sum_range _ e).symm
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hcoord : optionalCoordinate (n + k) (n + i.val) = MvPolynomial.X (Fin.natAdd n i) := by
      rw [optionalCoordinate, dite_eq_left (Nat.add_lt_add_left i.isLt n)]
      rfl
    rw [hcoord]

theorem exists_indexedEquationPositivityPolynomial_zero_iff
    (P Q : ℕ → MvPolynomial (Fin n) ℤ) (e k : ℕ) :
    (∃ z : Fin (n + k) → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) z
      (indexedEquationPositivityPolynomial P Q e k) = 0) ↔
      ∃ x : Fin n → ℝ, (∀ i < e, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (P i) = 0) ∧
        ∀ i < k, 0 < MvPolynomial.eval₂ (Int.castRingHom ℝ) x (Q i) := by
  rw [indexedEquationPositivityPolynomial_eq, exists_equationPositivityPolynomial_zero_iff]
  simp only [Fin.forall_iff]

end LeanCanny.CountingHierarchy
