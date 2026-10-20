/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PartialDerivativeDegree
public import LeanCanny.Algebra.WeightedHomogenization
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Adjoining the reciprocal of a polynomial's partial derivative

The new coordinate is at `none`. The equation u*partial_base(p)-1 forces the
partial derivative to be nonzero, and determines u uniquely over a field.
Its coefficients require only one derivative coefficient or the constant -1.
-/

@[expose] public section

namespace LeanCanny.Algebra.ReciprocalEquation
open MvPolynomial
open scoped Classical

variable {σ R : Type*} [CommRing R]

theorem optionEquiv_rename (p : MvPolynomial σ R) :
    optionEquivLeft R σ (rename some p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [rename_C, optionEquivLeft_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, rename_X, hp, optionEquivLeft_X_some]

theorem coefficient_rename (p : MvPolynomial σ R) (m : Option σ →₀ ℕ) :
    (rename some p).coeff m = if m none = 0 then p.coeff m.some else 0 := by
  rw [← optionEquivLeft_coeff_some_coeff_none R σ m (rename some p), optionEquiv_rename]
  by_cases h : m none = 0
  · simp only [Polynomial.coeff_C, h, ite_true]
  · simp only [Polynomial.coeff_C, h, ite_false]
    rfl

theorem coefficient_X_rename (p : MvPolynomial σ R) (m : Option σ →₀ ℕ) :
    (X none * rename some p).coeff m = if m none = 1 then p.coeff m.some else 0 := by
  rw [← optionEquivLeft_coeff_some_coeff_none R σ m (X none * rename some p),
    map_mul, optionEquivLeft_X_none, optionEquiv_rename, mul_comm Polynomial.X, Polynomial.coeff_C_mul_X]
  by_cases h : m none = 1
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    rfl

noncomputable def polynomial (p : MvPolynomial σ R) (base : σ) : MvPolynomial (Option σ) R :=
  X none * rename some (pderiv base p) - 1

theorem coefficient (p : MvPolynomial σ R) (base : σ) (m : Option σ →₀ ℕ) :
    (polynomial p base).coeff m =
      (if m none = 1 then (pderiv base p).coeff m.some else 0) - if 0 = m then 1 else 0 := by
  classical
  simp only [polynomial, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coefficient_X_rename,
    MvPolynomial.coeff_one]

theorem coefficient_branch (p : MvPolynomial σ R) (base : σ) (m : Option σ →₀ ℕ) :
    (polynomial p base).coeff m =
      if m none = 1 then (pderiv base p).coeff m.some else if m = 0 then -1 else 0 := by
  rw [coefficient]
  by_cases h : m none = 1
  · have hn : m ≠ 0 := by intro hz; simp [hz] at h
    simp [h, Ne.symm hn]
  · simp only [h, ite_false, zero_sub]
    by_cases hz : m = 0
    · simp [hz]
    · simp [hz, Ne.symm hz]

theorem degree_le [Nontrivial R] (p : MvPolynomial σ R) (base : σ) :
    (polynomial p base).totalDegree ≤ max p.totalDegree 1 := by
  have hd := PartialDerivativeDegree.degree_le p base
  have hr := MvPolynomial.totalDegree_rename_le (some : σ → Option σ) (pderiv base p)
  have hm := MvPolynomial.totalDegree_mul (X none : MvPolynomial (Option σ) R) (rename some (pderiv base p))
  have hs := MvPolynomial.totalDegree_sub (X none * rename some (pderiv base p)) (1 : MvPolynomial (Option σ) R)
  simp only [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_one] at hm hs
  change (X none * rename some (pderiv base p) - 1).totalDegree ≤ _
  omega

theorem eval {K : Type*} [CommRing K] (p : MvPolynomial σ R) (base : σ) (φ : R →+* K)
    (x : σ → K) (u : K) :
    (polynomial p base).eval₂ φ (fun i => i.elim u x) = u * (pderiv base p).eval₂ φ x - 1 := by
  simp only [polynomial, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
    Option.elim_none, MvPolynomial.eval₂_rename, MvPolynomial.eval₂_one]
  rfl

theorem root_iff {K : Type*} [Field K] (p : MvPolynomial σ R) (base : σ) (φ : R →+* K)
    (x : σ → K) (u : K) :
    (polynomial p base).eval₂ φ (fun i => i.elim u x) = 0 ↔
      (pderiv base p).eval₂ φ x ≠ 0 ∧ u = ((pderiv base p).eval₂ φ x)⁻¹ := by
  rw [eval, sub_eq_zero]
  constructor
  · intro h
    exact ⟨right_ne_zero_of_mul_eq_one h, eq_inv_of_mul_eq_one_left h⟩
  · rintro ⟨h, rfl⟩
    exact inv_mul_cancel₀ h

theorem exists_root_iff {K : Type*} [Field K] (p : MvPolynomial σ R) (base : σ) (φ : R →+* K)
    (x : σ → K) : (∃ u, (polynomial p base).eval₂ φ (fun i => i.elim u x) = 0) ↔
      (pderiv base p).eval₂ φ x ≠ 0 := by
  simp only [root_iff]
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

end LeanCanny.Algebra.ReciprocalEquation
