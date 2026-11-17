/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ReservedPrefixOrder
public import LeanCanny.CountingHierarchy.EncodedTermPolynomial

/-! # Finite counterexample variables and a frozen real parameter prefix -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial LeanCanny.ETR

variable {M r : ℕ}

def finiteFiberEnvironment (hr : r ≤ M) (x : Fin r → ℝ) (z : Fin (M - r) → ℝ) (i : ℕ) : ℝ :=
  if h : i < M then if hp : i < r then x ⟨i, hp⟩
    else z ⟨i - r, by omega⟩ else 0

theorem eval_reservedPrefix_term (t : Term) (hr : r ≤ M) (x : Fin r → ℝ) (z : Fin (M - r) → ℝ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x)
      (reservedPrefixPolynomial (t.finitePolynomial M) hr) = t.eval (finiteFiberEnvironment hr x z) := by
  rw [eval_reservedPrefixPolynomial, TermEvaluation.eval_finitePolynomial_ring]
  rfl

theorem term_prefix_fiber_iff_finite (t : Term) (ht : t.arity ≤ M) (hr : r ≤ M) (x : Fin r → ℝ) :
    (∃ env : ℕ → ℝ, (∀ i : Fin r, env i.val = x i) ∧ t.eval env = 0) ↔
      ∃ z : Fin (M - r) → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x)
        (reservedPrefixPolynomial (t.finitePolynomial M) hr) = 0 := by
  constructor
  · rintro ⟨env, hp, he⟩
    let z : Fin (M - r) → ℝ := fun i => env (r + i.val)
    refine ⟨z, ?_⟩
    rw [eval_reservedPrefix_term]
    have heq : t.eval (finiteFiberEnvironment hr x z) = t.eval env := by
      apply Term.eval_congr
      intro i hi
      have hiM : i < M := hi.trans_le ht
      rw [finiteFiberEnvironment, dite_eq_left hiM]
      by_cases hip : i < r
      · rw [dite_eq_left hip]
        exact (hp ⟨i, hip⟩).symm
      · rw [dite_eq_right hip]
        dsimp only [z]
        rw [Nat.add_sub_of_le (by omega : r ≤ i)]
    exact heq.trans he
  · rintro ⟨z, hz⟩
    refine ⟨finiteFiberEnvironment hr x z, ?_, ?_⟩
    · intro i
      have hiM : i.val < M := i.isLt.trans_le hr
      rw [finiteFiberEnvironment, dite_eq_left hiM, dite_eq_left i.isLt]
    · rwa [eval_reservedPrefix_term] at hz

end LeanCanny.CountingHierarchy
