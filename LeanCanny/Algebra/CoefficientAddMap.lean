/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogeneousSubstitution
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Additive coefficient transformations of homogeneous polynomials

A fixed denominator-clearing map is additive, without being multiplicative.
Applying it coefficientwise preserves support bounds and homogeneity. Scalar
compatibility of coefficient evaluation lifts to the full polynomial.
-/

@[expose] public section

namespace LeanCanny.Algebra.CoefficientAddMap
open MvPolynomial
open scoped Classical

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S]

noncomputable def apply (f : R →+ S) (p : MvPolynomial σ R) : MvPolynomial σ S := AddMonoidAlgebra.map f p

@[simp] theorem coeff (f : R →+ S) (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (apply f p).coeff m = f (p.coeff m) := rfl

theorem support_subset (f : R →+ S) (p : MvPolynomial σ R) : (apply f p).support ⊆ p.support := by
  intro m hm
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  have h := MvPolynomial.mem_support_iff.mp hm
  rw [coeff, hz, map_zero] at h
  exact h rfl

theorem homogeneous (f : R →+ S) (p : MvPolynomial σ R) (D : ℕ) (hp : p.IsHomogeneous D) :
    (apply f p).IsHomogeneous D := by
  intro m hm
  exact hp (MvPolynomial.mem_support_iff.mp (support_subset f p (MvPolynomial.mem_support_iff.mpr hm)))

theorem map_eq_smul {K : Type*} [CommSemiring K] (f : R →+ S) (p : MvPolynomial σ R)
    (φ : S →+* K) (ψ : R →+* K) (a : K)
    (h : ∀ m ∈ p.support, φ (f (p.coeff m)) = a * ψ (p.coeff m)) :
    (apply f p).map φ = a • p.map ψ := by
  ext m
  simp only [MvPolynomial.coeff_map, coeff, MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ p.support
  · exact h m hm
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero, map_zero, map_zero, mul_zero]

end LeanCanny.Algebra.CoefficientAddMap
