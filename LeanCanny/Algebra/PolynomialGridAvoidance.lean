/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Nullstellensatz

/-! # Finite integer grids avoiding polynomial exceptional sets

A nonzero polynomial does not vanish on a product of sets larger than its
coordinate degrees. In characteristic zero, coordinates in `0,...,b` suffice
when b bounds the total degree. Products handle finite families of conditions.
This supplies finite candidates once a suitable exceptional-degree bound is
available; it does not supply that bound for Canny's systems.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialGridAvoidance
open MvPolynomial
open scoped BigOperators

variable {R ι : Type*} [CommRing R] [IsDomain R] [Finite ι]

theorem exists_on_grid (p : MvPolynomial ι R) (hp : p ≠ 0) (S : ι → Finset R)
    (hdegree : ∀ i, p.degreeOf i < (S i).card) :
    ∃ x : ι → R, (∀ i, x i ∈ S i) ∧ MvPolynomial.eval x p ≠ 0 := by
  classical
  by_contra hn
  apply hp
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset p S hdegree
  intro x hx
  by_contra he
  exact hn ⟨x, hx, he⟩

theorem exists_nat_eval_ne_zero [CharZero R] (p : MvPolynomial ι R) (hp : p ≠ 0)
    (b : ℕ) (hb : p.totalDegree ≤ b) :
    ∃ u : ι → ℕ, (∀ i, u i ≤ b) ∧ MvPolynomial.eval (fun i => (u i : R)) p ≠ 0 := by
  classical
  let S : ι → Finset R := fun _ => (Finset.range (b + 1)).image (fun n : ℕ => (n : R))
  have hcard (i : ι) : (S i).card = b + 1 := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  obtain ⟨x, hx, he⟩ := exists_on_grid p hp S (fun i => by
    rw [hcard i]
    exact Nat.lt_succ_of_le ((degreeOf_le_totalDegree p i).trans hb))
  choose u hu hcast using fun i => Finset.mem_image.mp (hx i)
  refine ⟨u, fun i => Nat.le_of_lt_succ (Finset.mem_range.mp (hu i)), ?_⟩
  have hfun : (fun i => (u i : R)) = x := funext hcast
  rwa [hfun]

theorem exists_nat_common_nonzero [CharZero R] {σ : Type*} [Fintype σ]
    (p : σ → MvPolynomial ι R) (hp : ∀ j, p j ≠ 0) (b : ℕ)
    (hb : ∑ j, (p j).totalDegree ≤ b) :
    ∃ u : ι → ℕ, (∀ i, u i ≤ b) ∧ ∀ j, MvPolynomial.eval (fun i => (u i : R)) (p j) ≠ 0 := by
  classical
  have hprod : (∏ j, p j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)
  have hdegree : (∏ j, p j).totalDegree ≤ b := (totalDegree_finsetProd Finset.univ p).trans hb
  obtain ⟨u, hu, he⟩ := exists_nat_eval_ne_zero (∏ j, p j) hprod b hdegree
  rw [map_prod] at he
  exact ⟨u, hu, fun j => Finset.prod_ne_zero_iff.mp he j (Finset.mem_univ j)⟩

end LeanCanny.Algebra.PolynomialGridAvoidance
