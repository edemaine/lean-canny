/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionMap
public import LeanCanny.Algebra.RationalSubstitutionBounds

/-! # Explicit clearing allowances preserve evaluations and admit uniform budgets

The allowances may exceed the actual variable degrees and remain unchanged
under coefficient reduction. Degree and coefficient-mass estimates depend on
the supplied allowances and coordinate bounds, without recomputing degrees.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution
open Polynomial
open scoped BigOperators Classical
variable {σ R : Type*} [Fintype σ] [CommSemiring R]

theorem natDegree_clearedWith_le (D : σ → ℕ) (p : MvPolynomial σ R) (n d : σ → R[X])
    (hD : ∀ i, p.degreeOf i ≤ D i) (E : ℕ)
    (hn : ∀ i, (n i).natDegree ≤ E) (hd : ∀ i, (d i).natDegree ≤ E) :
    (clearedWith D p n d).natDegree ≤ (∑ i, 2 * D i) * E := by
  rw [Finset.sum_mul]
  exact (natDegree_clearedWith_le_sum D p n d hD).trans
    (Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (max_le (hn i) (hd i))))

theorem coefficientMass_clearedWith_le_pow (D : σ → ℕ) (p : MvPolynomial σ ℤ)
    (n d : σ → ℤ[X]) (hD : ∀ i, p.degreeOf i ≤ D i) (s b : ℕ)
    (hp : sourceMass p ≤ 2 ^ s)
    (hn : ∀ i, coefficientMass (n i) ≤ 2 ^ b) (hd : ∀ i, coefficientMass (d i) ≤ 2 ^ b) :
    coefficientMass (clearedWith D p n d) ≤ 2 ^ (s + (∑ i, 2 * D i) * b) := by
  calc
    _ ≤ sourceMass p * ∏ i, (2 ^ b) ^ (2 * D i) :=
      coefficientMass_clearedWith_le D p n d hD _ hn hd
    _ ≤ 2 ^ s * ∏ i, (2 ^ b) ^ (2 * D i) := Nat.mul_le_mul_right _ hp
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, ← pow_add, Nat.mul_comm b]

end LeanCanny.Algebra.RationalSubstitution
