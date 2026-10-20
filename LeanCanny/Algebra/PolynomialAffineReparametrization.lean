/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

/-! # A division-free affine reparametrization preserving the lowest coefficient

Homogenize to degree n, then substitute (X, 1-X). The i-th monomial becomes
its original coefficient times X^i (1-X)^(n-i). When the original degree is at
most n, both the lowest nonzero order and its coefficient are preserved.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialAffineReparametrization
open Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable def substitution : MvPolynomial (Fin 2) R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1 - Polynomial.X]

noncomputable def transform (p : Polynomial R) (n : ℕ) : Polynomial R := substitution (p.homogenize n)

theorem transform_zero (n : ℕ) : transform (0 : Polynomial R) n = 0 := by simp [transform]

theorem transform_monomial (r : R) (i n : ℕ) (hi : i ≤ n) :
    transform (Polynomial.monomial i r) n = Polynomial.C r * Polynomial.X ^ i * (1 - Polynomial.X) ^ (n - i) := by
  rw [transform, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.homogenize_C_mul, Polynomial.homogenize_X_pow hi]
  simp [substitution, mul_assoc]

theorem transform_sum (p : Polynomial R) (n : ℕ) (hp : p.natDegree ≤ n) :
    transform p n = ∑ i ∈ Finset.range (n + 1), Polynomial.C (p.coeff i) * Polynomial.X ^ i * (1 - Polynomial.X) ^ (n - i) := by
  have he := p.as_sum_range' (n + 1) (Nat.lt_succ_of_le hp)
  calc
    transform p n = transform (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (p.coeff i)) n := congrArg (fun q => transform q n) he
    _ = _ := by
      simp only [transform, Polynomial.homogenize_finsetSum, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact transform_monomial _ _ _ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

theorem coefficient_of_zero_prefix (p : Polynomial R) (n k : ℕ) (hp : p.natDegree ≤ n) (hk : k ≤ n)
    (hz : ∀ i < k, p.coeff i = 0) : (transform p n).coeff k = p.coeff k := by
  rw [transform_sum p n hp, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', ite_eq_left (le_refl k), Nat.sub_self]
    simp [Polynomial.coeff_zero_eq_eval_zero]
  · intro i _ hik
    rcases lt_or_gt_of_ne hik with hi | hi
    · rw [hz i hi, Polynomial.C_0, zero_mul, zero_mul, Polynomial.coeff_zero]
    · rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', ite_eq_right (Nat.not_le.mpr hi), mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))

theorem preserves_lowest (p : Polynomial R) (n : ℕ) (hp : p.natDegree ≤ n) :
    (transform p n).natTrailingDegree = p.natTrailingDegree ∧ (transform p n).trailingCoeff = p.trailingCoeff := by
  by_cases hzero : p = 0
  · simp [hzero, transform_zero]
  have ht : p.natTrailingDegree ≤ n := p.natTrailingDegree_le_natDegree.trans hp
  have hc : (transform p n).coeff p.natTrailingDegree = p.trailingCoeff :=
    coefficient_of_zero_prefix p n _ hp ht (fun _ hi => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi)
  have hcn : (transform p n).coeff p.natTrailingDegree ≠ 0 := by
    rw [hc]
    exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hzero
  have hpn : transform p n ≠ 0 := by
    intro hz
    exact hcn (by rw [hz, Polynomial.coeff_zero])
  have he : (transform p n).natTrailingDegree = p.natTrailingDegree := by
    apply le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hcn)
    apply Polynomial.le_natTrailingDegree hpn
    intro i hi
    rw [coefficient_of_zero_prefix p n i hp (by omega)
      (fun j hj => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega))]
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi
  refine ⟨he, ?_⟩
  simpa only [Polynomial.trailingCoeff, he] using hc

end LeanCanny.Algebra.PolynomialAffineReparametrization
