/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.MvMassNsmul
public import LeanCanny.Algebra.MvCoefficientMass
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic.Ring

/-! # Integer coefficient mass with multivariate parameters

The sum of multivariate integer coefficient masses bounds each coefficient and is subadditive
and submultiplicative. Renaming cannot increase it, even when variables merge.
A partial derivative increases mass by at most the polynomial's total degree.
-/

@[expose] public section

namespace LeanCanny.CountingHierarchy.MultivariateParameterMass
open MvPolynomial LeanCanny.Algebra
open scoped BigOperators

variable {ι κ τ : Type*}

noncomputable def mass (p : MvPolynomial ι (MvPolynomial τ ℤ)) : ℕ := ∑ m ∈ p.support, MvMass.mass (p.coeff m)

@[simp] theorem zero : mass (0 : MvPolynomial ι (MvPolynomial τ ℤ)) = 0 := by simp [mass]

@[simp] theorem monomial (m : ι →₀ ℕ) (a : MvPolynomial τ ℤ) : mass (MvPolynomial.monomial m a) = MvMass.mass a := by
  rw [mass, ← MvPolynomial.sum_def]
  exact MvPolynomial.sum_monomial_eq (by simp)

@[simp] theorem C (a : MvPolynomial τ ℤ) : mass (MvPolynomial.C a : MvPolynomial ι (MvPolynomial τ ℤ)) = MvMass.mass a := monomial 0 a
@[simp] theorem one : mass (1 : MvPolynomial ι (MvPolynomial τ ℤ)) = 1 := by
  rw [← MvPolynomial.C_1, C, ← MvPolynomial.C_1, MvMass.C]
  rfl
@[simp] theorem X (i : ι) : mass (MvPolynomial.X i : MvPolynomial ι (MvPolynomial τ ℤ)) = 1 := by
  change mass (MvPolynomial.monomial (Finsupp.single i 1) 1) = 1
  rw [monomial, ← MvPolynomial.C_1, MvMass.C]
  rfl

/-- Promoting integer coefficients to constant multivariate parameter polynomials preserves mass. -/
@[simp] theorem map_C (p : MvPolynomial ι ℤ) :
    mass (p.map (MvPolynomial.C : ℤ →+* MvPolynomial τ ℤ)) = LeanCanny.Algebra.MvMass.mass p := by
  rw [mass, MvPolynomial.support_map_of_injective p (MvPolynomial.C_injective τ ℤ)]
  simp only [MvPolynomial.coeff_map, MvMass.C]
  rfl

theorem coeff_le (p : MvPolynomial ι (MvPolynomial τ ℤ)) (m : ι →₀ ℕ) : MvMass.mass (p.coeff m) ≤ mass p := by
  classical
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (f := fun m => MvMass.mass (p.coeff m)) (fun _ _ => Nat.zero_le _) hm
  · simp only [notMem_support_iff.mp hm, MvMass.zero, Nat.zero_le]

theorem mass_eq_sum (p : MvPolynomial ι (MvPolynomial τ ℤ)) (s : Finset (ι →₀ ℕ)) (hs : p.support ⊆ s) :
    mass p = ∑ m ∈ s, MvMass.mass (p.coeff m) := by
  classical
  apply Finset.sum_subset hs
  intro m _ hm
  simp only [notMem_support_iff.mp hm, MvMass.zero]

theorem add_le (p q : MvPolynomial ι (MvPolynomial τ ℤ)) : mass (p + q) ≤ mass p + mass q := by
  classical
  let s := p.support ∪ q.support
  rw [mass_eq_sum (p + q) s (fun _ h => support_add h), mass_eq_sum p s Finset.subset_union_left,
    mass_eq_sum q s Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun m _ => by
    simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using MvMass.add_le (p.coeff m) (q.coeff m)

@[simp] theorem neg (p : MvPolynomial ι (MvPolynomial τ ℤ)) : mass (-p) = mass p := by
  simp [mass]

theorem sub_le (p q : MvPolynomial ι (MvPolynomial τ ℤ)) : mass (p - q) ≤ mass p + mass q := by
  simpa only [sub_eq_add_neg, neg] using add_le p (-q)

theorem sum_le {J : Type*} (s : Finset J) (p : J → MvPolynomial ι (MvPolynomial τ ℤ)) :
    mass (∑ j ∈ s, p j) ≤ ∑ j ∈ s, mass (p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (add_le _ _).trans (Nat.add_le_add_left ih _)

theorem mul_le (p q : MvPolynomial ι (MvPolynomial τ ℤ)) : mass (p * q) ≤ mass p * mass q := by
  classical
  conv_lhs => rw [p.as_sum, q.as_sum]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, monomial_mul_monomial]
  apply (sum_le _ _).trans
  apply (Finset.sum_le_sum (fun m _ => sum_le q.support _)).trans
  simp only [monomial]
  apply (Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun j _ =>
    MvMass.mul_le (p.coeff m) (q.coeff j)))).trans
  rw [mass, mass, Finset.sum_mul]
  simp only [Finset.mul_sum, le_refl]

theorem pow_le (p : MvPolynomial ι (MvPolynomial τ ℤ)) (n : ℕ) : mass (p ^ n) ≤ mass p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

theorem prod_le {J : Type*} (s : Finset J) (p : J → MvPolynomial ι (MvPolynomial τ ℤ)) :
    mass (∏ j ∈ s, p j) ≤ ∏ j ∈ s, mass (p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact (mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem rename_le (f : ι → κ) (p : MvPolynomial ι (MvPolynomial τ ℤ)) : mass (rename f p) ≤ mass p := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply (sum_le _ _).trans
  simp only [rename_monomial, monomial]
  exact le_rfl

theorem pderiv_le (p : MvPolynomial ι (MvPolynomial τ ℤ)) (i : ι) : mass (pderiv i p) ≤ p.totalDegree * mass p := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply (sum_le _ _).trans
  rw [mass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  rw [pderiv_monomial, monomial, mul_comm, ← nsmul_eq_mul, MvMass.mass_nsmul]
  apply Nat.mul_le_mul_right
  exact (Finsupp.single_eval_le_sum m rfl (fun _ => Nat.zero_le _) i).trans (le_totalDegree hm)

end LeanCanny.CountingHierarchy.MultivariateParameterMass
