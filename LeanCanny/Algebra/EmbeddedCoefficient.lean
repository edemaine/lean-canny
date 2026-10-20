/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Finsupp.Order

/-! # Coefficients after an injective variable embedding

Coordinates outside the embedding must have exponent zero. Otherwise the
coefficient vanishes; on the embedded coordinates a single source query
suffices. Multiplication by one variable shifts that query by one.
-/

@[expose] public section

namespace LeanCanny.Algebra.EmbeddedCoefficient
open MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

noncomputable def value (f : σ → τ) (hf : Function.Injective f) (p : MvPolynomial σ R) (m : τ →₀ ℕ) : R := by
  classical
  exact if (↑m.support : Set τ) ⊆ Set.range f then p.coeff (m.comapDomain f hf.injOn) else 0

theorem coeff_rename (f : σ → τ) (hf : Function.Injective f) (p : MvPolynomial σ R) (m : τ →₀ ℕ) :
    (rename f p).coeff m = value f hf p m := by
  classical
  unfold value
  split_ifs with h
  · have hm := Finsupp.mapDomain_comapDomain f hf m h
    conv_lhs => rw [← hm]
    exact MvPolynomial.coeff_rename_mapDomain f hf p _
  · apply MvPolynomial.coeff_rename_eq_zero
    intro u hu
    exfalso
    apply h
    intro j hj
    rw [← hu] at hj
    exact Finsupp.mem_range_of_mapDomain_ne_zero (Finsupp.mem_support_iff.mp hj)

theorem value_mapDomain (f : σ → τ) (hf : Function.Injective f) (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    value f hf p (m.mapDomain f) = p.coeff m := by
  rw [← coeff_rename]
  exact MvPolynomial.coeff_rename_mapDomain f hf p m

noncomputable def shift (p : MvPolynomial σ R) (m : σ →₀ ℕ) (i : σ) : R := by
  classical
  exact if i ∈ m.support then p.coeff (m - Finsupp.single i 1) else 0

theorem coeff_mul_C_X (p : MvPolynomial σ R) (a : R) (i : σ) (m : σ →₀ ℕ) :
    (p * (C a * X i)).coeff m = a * shift p m i := by
  classical
  rw [show p * (C a * X i) = C a * (p * X i) by ac_rfl, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']
  rfl

noncomputable def derivative (f : σ → τ) (hf : Function.Injective f) (p : MvPolynomial σ R)
    (i : σ) (m : τ →₀ ℕ) : R := by
  classical
  let u := m.comapDomain f hf.injOn
  exact if (↑m.support : Set τ) ⊆ Set.range f then p.coeff (u + Finsupp.single i 1) * (u i + 1) else 0

theorem coeff_rename_pderiv (f : σ → τ) (hf : Function.Injective f) (p : MvPolynomial σ R)
    (i : σ) (m : τ →₀ ℕ) : (rename f (pderiv i p)).coeff m = derivative f hf p i m := by
  classical
  rw [coeff_rename f hf]
  unfold value derivative
  split_ifs <;> simp only [MvPolynomial.coeff_pderiv]

end LeanCanny.Algebra.EmbeddedCoefficient
