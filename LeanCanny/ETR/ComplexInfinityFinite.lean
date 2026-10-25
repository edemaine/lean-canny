/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexInfinityCorrect
public import Mathlib.Algebra.BigOperators.Fin

/-! # Finite-coordinate semantics of infinity-chart circuits -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Infinity
open scoped Classical BigOperators

theorem query_satisfiable_fin (n : ℕ) (bits : List Bool) (v : ℕ → ℤ) (i : Fin (n + 1)) :
    Satisfiable (query (n + 1) bits v i.val) ↔
      ∃ x : Fin (n + 1) → ℂ, x i = 1 ∧ (∑ j : Fin (n + 1), x j ^ (Nat.fromBitsLE bits + 1)) = 0 ∧
        ∀ j : Fin n, x j.succ ^ Nat.fromBitsLE bits - (v (j.val + 1) : ℂ) * x 0 ^ Nat.fromBitsLE bits = 0 := by
  rw [query_satisfiable (n + 1) (by omega) bits v i.val i.isLt]
  constructor
  · rintro ⟨x, hx, hs, hd⟩
    refine ⟨fun j => x j.val, hx, ?_, ?_⟩
    · exact (Fin.sum_univ_eq_sum_range (fun j => x j ^ (Nat.fromBitsLE bits + 1)) (n + 1)).trans hs
    · intro j
      exact hd (j.val + 1) (by omega) j.succ.isLt
  · rintro ⟨x, hx, hs, hd⟩
    let e : ℕ → ℂ := fun j => if h : j < n + 1 then x ⟨j, h⟩ else 0
    refine ⟨e, ?_, ?_, ?_⟩
    · simpa only [e, i.isLt, dite_true, Fin.eta] using hx
    · rw [← Fin.sum_univ_eq_sum_range]
      simpa only [e, Fin.is_lt, dite_true, Fin.eta] using hs
    · intro j hj0 hjm
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj0)
      have hjn : j < n := by omega
      simpa [e, hjm, hjn] using hd (⟨j, hjn⟩ : Fin n)

end LeanCanny.ETR.ComplexCircuit.Infinity
