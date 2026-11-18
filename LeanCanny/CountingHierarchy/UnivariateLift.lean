/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled
public import LeanCanny.Algebra.CoefficientMass
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Univariate polynomials as controlled-family specifications -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial MvPolynomial LeanCanny.Algebra
open scoped BigOperators Classical

noncomputable def liftUnivariate : Polynomial ℤ →+* MvPolynomial (Fin 1) ℤ :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)

theorem liftUnivariate_monomial (i : ℕ) (a : ℤ) :
    liftUnivariate (Polynomial.monomial i a) = MvPolynomial.C a * MvPolynomial.X 0 ^ i :=
  Polynomial.eval₂_monomial _ _

theorem liftUnivariate_degree_le (p : Polynomial ℤ) : (liftUnivariate p).totalDegree ≤ p.natDegree := by
  conv_lhs => rw [p.as_sum_range, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  rw [liftUnivariate_monomial]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have h := MvPolynomial.totalDegree_pow (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℤ) i
  simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, Nat.mul_one, Nat.zero_add] at h ⊢
  have := Finset.mem_range.mp hi
  omega

theorem liftUnivariate_mass_le (p : Polynomial ℤ) : MvMass.mass (liftUnivariate p) ≤ coefficientMass p := by
  conv_lhs => rw [p.as_sum_range, map_sum]
  apply (MvMass.sum_le _ _).trans
  rw [show coefficientMass p = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).natAbs from
    p.sum_over_range' (fun _ => rfl) _ (Nat.lt_succ_self _)]
  apply Finset.sum_le_sum
  intro i _
  rw [liftUnivariate_monomial]
  exact (MvMass.mul_le _ _).trans (by
    simpa only [MvMass.C, MvMass.X, one_pow, Nat.mul_one] using
      Nat.mul_le_mul_left (p.coeff i).natAbs (MvMass.pow_le (MvPolynomial.X (0 : Fin 1)) i))

theorem liftUnivariate_coeff (p : Polynomial ℤ) (k : ℕ) :
    (liftUnivariate p).coeff (Finsupp.single 0 k) = p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
  | monomial i a =>
    rw [liftUnivariate_monomial, MvPolynomial.C_mul_X_pow_eq_monomial]
    simp only [MvPolynomial.coeff_monomial, Polynomial.coeff_monomial, Finsupp.single_apply,
      (Finsupp.single_injective (0 : Fin 1)).eq_iff]

theorem liftUnivariate_degree_eq (p : Polynomial ℤ) : (liftUnivariate p).totalDegree = p.natDegree := by
  apply le_antisymm (liftUnivariate_degree_le p)
  by_cases hp : p = 0
  · simp only [hp, Polynomial.natDegree_zero, Nat.zero_le]
  · have hmem : Finsupp.single (0 : Fin 1) p.natDegree ∈ (liftUnivariate p).support := by
      rw [MvPolynomial.mem_support_iff, liftUnivariate_coeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp
    simpa only [Finsupp.sum_single_index] using MvPolynomial.le_totalDegree hmem

theorem liftUnivariate_mass_eq (p : Polynomial ℤ) : MvMass.mass (liftUnivariate p) = coefficientMass p := by
  apply le_antisymm (liftUnivariate_mass_le p)
  have hinj : Function.Injective (Finsupp.single (0 : Fin 1) : ℕ → (Fin 1 →₀ ℕ)) := Finsupp.single_injective 0
  have hs : p.support.image (Finsupp.single (0 : Fin 1)) ⊆ (liftUnivariate p).support := by
    rintro e he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    rw [MvPolynomial.mem_support_iff, liftUnivariate_coeff]
    exact Polynomial.mem_support_iff.mp hk
  change (∑ k ∈ p.support, (p.coeff k).natAbs) ≤ _
  calc
    _ = ∑ e ∈ p.support.image (Finsupp.single (0 : Fin 1)), ((liftUnivariate p).coeff e).natAbs := by
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
      simp only [liftUnivariate_coeff]
    _ ≤ MvMass.mass (liftUnivariate p) :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)

theorem eval_liftUnivariate {S : Type*} [CommRing S] (phi : ℤ →+* S) (z : Fin 1 → S) (p : Polynomial ℤ) :
    MvPolynomial.eval₂ phi z (liftUnivariate p) = p.eval₂ phi (z 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, MvPolynomial.eval₂_add, Polynomial.eval₂_add, hp, hq]
  | monomial i a =>
    rw [liftUnivariate_monomial]
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow,
      MvPolynomial.eval₂_X, Polynomial.eval₂_monomial]

end LeanCanny.CountingHierarchy
