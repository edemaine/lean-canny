/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MvCoefficientMass

/-! # Degree and coefficient mass under polynomial substitution -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial LeanCanny.Algebra
open scoped BigOperators Classical

variable {ι κ : Type*}

noncomputable def substitutePolynomial (s : ι → MvPolynomial κ ℤ) :
    MvPolynomial ι ℤ →+* MvPolynomial κ ℤ := MvPolynomial.eval₂Hom MvPolynomial.C s

theorem substitutePolynomial_mass_le (s : ι → MvPolynomial κ ℤ)
    (hs : ∀ i, MvMass.mass (s i) ≤ 1) (p : MvPolynomial ι ℤ) :
    MvMass.mass (substitutePolynomial s p) ≤ MvMass.mass p := by
  conv_lhs => rw [p.as_sum, map_sum]
  apply (MvMass.sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  change MvMass.mass ((MvPolynomial.monomial e (p.coeff e)).eval₂ MvPolynomial.C s) ≤ _
  rw [MvPolynomial.eval₂_monomial]
  apply (MvMass.mul_le _ _).trans
  have hprod : MvMass.mass (e.prod fun i k => s i ^ k) ≤ 1 := by
    apply (MvMass.prod_le _ _).trans
    apply (Finset.prod_le_prod (fun i _ =>
      (MvMass.pow_le _ _).trans ((Nat.pow_le_pow_left (hs i) _).trans_eq (one_pow _)))).trans_eq
    exact Finset.prod_const_one
  simpa only [MvMass.C, Nat.mul_one] using Nat.mul_le_mul_left (p.coeff e).natAbs hprod

theorem substitutePolynomial_degree_le (s : ι → MvPolynomial κ ℤ) (K : ℕ)
    (hs : ∀ i, (s i).totalDegree ≤ K) (p : MvPolynomial ι ℤ) :
    (substitutePolynomial s p).totalDegree ≤ K * p.totalDegree := by
  conv_lhs => rw [p.as_sum, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  change ((MvPolynomial.monomial e (p.coeff e)).eval₂ MvPolynomial.C s).totalDegree ≤ _
  rw [MvPolynomial.eval₂_monomial]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, Nat.zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ i ∈ e.support, e i * K := Finset.sum_le_sum (fun i _ =>
      (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hs i)))
    _ = K * e.sum (fun _ k => k) := by rw [Finsupp.sum, Nat.mul_comm K, Finset.sum_mul]
    _ ≤ K * p.totalDegree := Nat.mul_le_mul_left K (MvPolynomial.le_totalDegree he)

end LeanCanny.CountingHierarchy
