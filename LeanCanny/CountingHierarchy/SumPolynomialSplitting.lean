/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.MultivariateParameterMass
public import LeanCanny.CountingHierarchy.MultivariateParameterDegree
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Retaining one variable block as multivariate coefficients -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial LeanCanny.Algebra
open scoped BigOperators Classical

variable {ι κ : Type*}

namespace HasMultivariateParameterDegree

theorem prod_sum {J : Type*} (s : Finset J) (f : J → MvPolynomial ι (MvPolynomial κ ℤ))
    (H : J → ℕ) (hf : ∀ j ∈ s, HasMultivariateParameterDegree (f j) (H j)) :
    HasMultivariateParameterDegree (∏ j ∈ s, f j) (∑ j ∈ s, H j) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using (one (ι := ι) (τ := κ))
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self _ _)).mul (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

end HasMultivariateParameterDegree

noncomputable def splitIntegerPolynomial :
    MvPolynomial (ι ⊕ κ) ℤ ≃ₐ[ℤ] MvPolynomial ι (MvPolynomial κ ℤ) := MvPolynomial.sumAlgEquiv ℤ ι κ

@[simp] theorem splitIntegerPolynomial_C (z : ℤ) :
    (splitIntegerPolynomial (MvPolynomial.C z) : MvPolynomial ι (MvPolynomial κ ℤ)) = MvPolynomial.C (MvPolynomial.C z) :=
  MvPolynomial.sumAlgEquiv_C_inl ℤ ι κ z

@[simp] theorem splitIntegerPolynomial_X_inl (i : ι) :
    (splitIntegerPolynomial (MvPolynomial.X (.inl i)) : MvPolynomial ι (MvPolynomial κ ℤ)) = MvPolynomial.X i :=
  MvPolynomial.sumAlgEquiv_X_inl ℤ ι κ i

@[simp] theorem splitIntegerPolynomial_X_inr (i : κ) :
    (splitIntegerPolynomial (MvPolynomial.X (.inr i)) : MvPolynomial ι (MvPolynomial κ ℤ)) = MvPolynomial.C (MvPolynomial.X i) :=
  MvPolynomial.sumAlgEquiv_X_inr ℤ ι κ i

private theorem split_X_mass (i : ι ⊕ κ) :
    MultivariateParameterMass.mass (splitIntegerPolynomial (MvPolynomial.X i)) = 1 := by
  cases i <;> simp only [splitIntegerPolynomial_X_inl, splitIntegerPolynomial_X_inr,
    MultivariateParameterMass.X, MultivariateParameterMass.C, MvMass.X]

private theorem split_monomial_mass (e : (ι ⊕ κ) →₀ ℕ) (z : ℤ) :
    MultivariateParameterMass.mass (splitIntegerPolynomial (MvPolynomial.monomial e z)) ≤ z.natAbs := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod, map_mul, map_prod]
  simp only [map_pow, splitIntegerPolynomial_C]
  apply (MultivariateParameterMass.mul_le _ _).trans
  rw [MultivariateParameterMass.C, MvMass.C]
  have hp : MultivariateParameterMass.mass (∏ i ∈ e.support, splitIntegerPolynomial (MvPolynomial.X i) ^ e i) ≤ 1 := by
    apply (MultivariateParameterMass.prod_le _ _).trans
    calc
      _ ≤ ∏ _i ∈ e.support, 1 := by
        apply Finset.prod_le_prod
        intro i _
        exact (MultivariateParameterMass.pow_le _ _).trans_eq (by rw [split_X_mass, one_pow])
      _ = 1 := by simp
  exact (Nat.mul_le_mul_left _ hp).trans_eq (Nat.mul_one _)

theorem splitIntegerPolynomial_mass_le (p : MvPolynomial (ι ⊕ κ) ℤ) :
    MultivariateParameterMass.mass (splitIntegerPolynomial p) ≤ MvMass.mass p := by
  conv_lhs => rw [p.as_sum, map_sum]
  apply (MultivariateParameterMass.sum_le _ _).trans
  exact Finset.sum_le_sum (fun e _ => split_monomial_mass e (p.coeff e))

private theorem split_X_mainDegree (i : ι ⊕ κ) :
    (splitIntegerPolynomial (MvPolynomial.X i)).totalDegree ≤ 1 := by
  cases i <;> simp only [splitIntegerPolynomial_X_inl, splitIntegerPolynomial_X_inr,
    MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C, le_refl, Nat.zero_le]

private theorem split_monomial_mainDegree (e : (ι ⊕ κ) →₀ ℕ) (z : ℤ) :
    (splitIntegerPolynomial (MvPolynomial.monomial e z)).totalDegree ≤ e.sum (fun _ k => k) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod, map_mul, map_prod]
  simp only [map_pow, splitIntegerPolynomial_C]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, Nat.zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  apply Finset.sum_le_sum
  intro i _
  exact (MvPolynomial.totalDegree_pow _ _).trans
    ((Nat.mul_le_mul_left (e i) (split_X_mainDegree i)).trans_eq (Nat.mul_one _))

theorem splitIntegerPolynomial_mainDegree_le (p : MvPolynomial (ι ⊕ κ) ℤ) :
    (splitIntegerPolynomial p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  exact (split_monomial_mainDegree e (p.coeff e)).trans (MvPolynomial.le_totalDegree he)

private theorem split_X_parameterDegree (i : ι ⊕ κ) :
    HasMultivariateParameterDegree (splitIntegerPolynomial (MvPolynomial.X i)) 1 := by
  cases i with
  | inl i =>
    rw [splitIntegerPolynomial_X_inl]
    exact (HasMultivariateParameterDegree.X (τ := κ) i).mono (by omega)
  | inr i =>
    rw [splitIntegerPolynomial_X_inr]
    exact HasMultivariateParameterDegree.C _ (by simp)

private theorem split_monomial_parameterDegree (e : (ι ⊕ κ) →₀ ℕ) (z : ℤ) :
    HasMultivariateParameterDegree (splitIntegerPolynomial (MvPolynomial.monomial e z)) (e.sum (fun _ k => k)) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod, map_mul, map_prod]
  simp only [map_pow, splitIntegerPolynomial_C]
  have hc : HasMultivariateParameterDegree
      (MvPolynomial.C (MvPolynomial.C z) : MvPolynomial ι (MvPolynomial κ ℤ)) 0 :=
    HasMultivariateParameterDegree.C (MvPolynomial.C z) (by rw [MvPolynomial.totalDegree_C])
  have hp := HasMultivariateParameterDegree.prod_sum e.support
    (fun i => splitIntegerPolynomial (MvPolynomial.X i) ^ e i) (fun i => e i)
    (fun i _ => by simpa only [Nat.mul_one] using (split_X_parameterDegree i).pow (e i))
  simpa only [Finsupp.sum, Nat.zero_add] using hc.mul hp

theorem splitIntegerPolynomial_parameterDegree_le (p : MvPolynomial (ι ⊕ κ) ℤ) :
    HasMultivariateParameterDegree (splitIntegerPolynomial p) p.totalDegree := by
  conv_lhs => rw [p.as_sum, map_sum]
  apply HasMultivariateParameterDegree.sum
  intro e he
  exact (split_monomial_parameterDegree e (p.coeff e)).mono (MvPolynomial.le_totalDegree he)

end LeanCanny.CountingHierarchy
