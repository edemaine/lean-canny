/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Surjectivity from positive-degree exactness on fixed finite pieces

Two finite complexes on the same graded vector spaces, exact in positive
degrees and zero above a fixed degree, have the same differential ranks.
Thus surjectivity at degree zero for one implies it for the other.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteComplexSurjectivity
variable {K : Type*} [Field K] (V : ℕ → Type*) [∀ k, AddCommGroup (V k)] [∀ k, Module K (V k)]
  [∀ k, FiniteDimensional K (V k)]

theorem range_finrank_eq (d e : (k : ℕ) → V (k + 1) →ₗ[K] V k)
    (hd : ∀ k, LinearMap.ker (d k) = LinearMap.range (d (k + 1)))
    (he : ∀ k, LinearMap.ker (e k) = LinearMap.range (e (k + 1)))
    (N : ℕ) [Subsingleton (V (N + 1))] (k : ℕ) (hk : k ≤ N) :
    Module.finrank K (LinearMap.range (d k)) = Module.finrank K (LinearMap.range (e k)) := by
  have hr : ∀ m j : ℕ, m = N - j → j ≤ N →
      Module.finrank K (LinearMap.range (d j)) = Module.finrank K (LinearMap.range (e j)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro j hm hj
      by_cases hjN : j = N
      · subst j
        have hdN : d N = 0 := by ext x; rw [Subsingleton.elim x 0, map_zero]; rfl
        have heN : e N = 0 := by ext x; rw [Subsingleton.elim x 0, map_zero]; rfl
        rw [hdN, heN]
      · have hj' : j + 1 ≤ N := by omega
        have hnext := ih (N - (j + 1)) (by omega) (j + 1) rfl hj'
        have hdimd := (d j).finrank_range_add_finrank_ker
        have hdime := (e j).finrank_range_add_finrank_ker
        rw [hd j] at hdimd
        rw [he j] at hdime
        omega
  exact hr (N - k) k rfl hk

theorem surjective_of_exact (d e : (k : ℕ) → V (k + 1) →ₗ[K] V k)
    (hd : ∀ k, LinearMap.ker (d k) = LinearMap.range (d (k + 1)))
    (he : ∀ k, LinearMap.ker (e k) = LinearMap.range (e (k + 1)))
    (N : ℕ) [Subsingleton (V (N + 1))] (hs : Function.Surjective (e 0)) : Function.Surjective (d 0) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [range_finrank_eq V d e hd he N 0 (Nat.zero_le N), LinearMap.range_eq_top.mpr hs, finrank_top]

end LeanCanny.Algebra.FiniteComplexSurjectivity
