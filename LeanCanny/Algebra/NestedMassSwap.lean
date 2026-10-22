/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.NestedCoefficientMass
public import LeanCanny.Algebra.PolynomialKronecker

/-! # Coefficient mass is invariant under exchanging the two variables -/

@[expose] public section
namespace LeanCanny.Algebra.NestedMass
open Polynomial
open scoped BigOperators

private theorem rectangle (p : Polynomial (Polynomial ℤ)) (N M : ℕ)
    (hN : p.natDegree < N) (hM : ∀ j, (p.coeff j).natDegree < M) :
    mass p = ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range M, ((p.coeff j).coeff i).natAbs := by
  rw [range_sum p N hN]
  apply Finset.sum_congr rfl
  intro j _
  exact (p.coeff j).sum_over_range' (fun _ => rfl) M (hM j)

@[simp] theorem swap (p : Polynomial (Polynomial ℤ)) : mass (Polynomial.Bivariate.swap p) = mass p := by
  let N := p.natDegree + 1
  let M := (Polynomial.Bivariate.swap p).natDegree + 1
  have hp : ∀ j, (p.coeff j).natDegree < M := by
    intro j
    exact ((PolynomialKronecker.inner_degree_iff_swap p _).mpr le_rfl j).trans_lt (Nat.lt_succ_self _)
  have hq : ∀ j, ((Polynomial.Bivariate.swap p).coeff j).natDegree < N := by
    intro j
    apply ((PolynomialKronecker.inner_degree_iff_swap (Polynomial.Bivariate.swap p) _).mpr
      (by rw [Polynomial.Bivariate.swap_swap_apply]) j).trans_lt (Nat.lt_succ_self _)
  rw [rectangle (Polynomial.Bivariate.swap p) M N (Nat.lt_succ_self _) hq,
    rectangle p N M (Nat.lt_succ_self _) hp]
  simp only [PolynomialKronecker.swap_coefficient]
  exact Finset.sum_comm

end LeanCanny.Algebra.NestedMass
