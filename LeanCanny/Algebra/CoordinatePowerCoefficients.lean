/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinatePowerSubstitution
public import LeanCanny.Algebra.MvCoefficientMass
public import Mathlib.Data.Finsupp.Fintype

/-! # Exact coefficient access after coordinate-dependent powers

A requested exponent is divided independently by each coordinate's positive
power. A failed divisibility test gives zero; otherwise exactly one original
coefficient is read. No polynomial expansion or coefficient sum is needed.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoordinatePowerSubstitution
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

noncomputable def exponent (w : σ → ℕ) (e : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => e i * w i)

theorem exponent_apply (w : σ → ℕ) (e : σ →₀ ℕ) (i : σ) : exponent w e i = e i * w i := rfl

theorem exponent_injective (w : σ → ℕ) (hw : ∀ i, 0 < w i) : Function.Injective (exponent w) := by
  intro e f h
  ext i
  exact Nat.eq_of_mul_eq_mul_right (hw i) (congrArg (fun e => e i) h)

theorem substitute_monomial (w : σ → ℕ) (e : σ →₀ ℕ) (r : R) :
    substitute w (monomial e r) = monomial (exponent w e) r := by
  rw [substitute, bind₁_monomial, monomial_eq]
  congr 1
  change e.prod (fun i k => (X i ^ w i : MvPolynomial σ R) ^ k) =
    (exponent w e).prod (fun i k => (X i : MvPolynomial σ R) ^ k)
  rw [Finsupp.prod_fintype e _ (fun _ => pow_zero _),
    Finsupp.prod_fintype (exponent w e) _ (fun _ => pow_zero _)]
  simp only [exponent_apply, ← pow_mul, Nat.mul_comm]

theorem coefficient_scaled (w : σ → ℕ) (hw : ∀ i, 0 < w i) (p : MvPolynomial σ R) (e : σ →₀ ℕ) :
    (substitute w p).coeff (exponent w e) = p.coeff e := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
  | monomial f r => simp only [substitute_monomial, coeff_monomial, (exponent_injective w hw).eq_iff]

theorem support_subset (w : σ → ℕ) (p : MvPolynomial σ R) :
    (substitute w p).support ⊆ p.support.image (exponent w) := by
  conv_lhs => rw [p.as_sum, map_sum]
  simp only [substitute_monomial]
  refine MvPolynomial.support_sum.trans ?_
  aesop (add simp Finset.subset_iff)

theorem coefficient_zero_of_not_dvd (w : σ → ℕ) (p : MvPolynomial σ R) (m : σ →₀ ℕ)
    (i : σ) (hi : ¬w i ∣ m i) : (substitute w p).coeff m = 0 := by
  by_contra h
  have H := support_subset w p (MvPolynomial.mem_support_iff.mpr h)
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp H
  apply hi
  rw [← he, exponent_apply]
  exact dvd_mul_left _ _

noncomputable def quotientExponent (w : σ → ℕ) (m : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m i / w i)

theorem quotientExponent_apply (w : σ → ℕ) (m : σ →₀ ℕ) (i : σ) : quotientExponent w m i = m i / w i := rfl

theorem exponent_quotient (w : σ → ℕ) (m : σ →₀ ℕ) (hm : ∀ i, m i % w i = 0) :
    exponent w (quotientExponent w m) = m := by
  ext i
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (hm i))

theorem coefficient (w : σ → ℕ) (hw : ∀ i, 0 < w i) (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (substitute w p).coeff m = if ∀ i, m i % w i = 0 then p.coeff (quotientExponent w m) else 0 := by
  by_cases hm : ∀ i, m i % w i = 0
  · rw [ite_eq_left hm]
    conv_lhs => rw [← exponent_quotient w m hm]
    exact coefficient_scaled w hw p (quotientExponent w m)
  · rw [ite_eq_right hm]
    push Not at hm
    obtain ⟨i, hi⟩ := hm
    exact coefficient_zero_of_not_dvd w p m i (by simpa only [Nat.dvd_iff_mod_eq_zero] using hi)

theorem mass_le (w : σ → ℕ) (p : MvPolynomial σ ℤ) : MvMass.mass (substitute w p) ≤ MvMass.mass p := by
  calc
    _ ≤ ∑ e ∈ p.support, MvMass.mass (substitute w (monomial e (p.coeff e))) := by
      conv_lhs => rw [p.as_sum, map_sum]
      exact MvMass.sum_le _ _
    _ = MvMass.mass p := by
      simp only [substitute_monomial, MvMass.monomial]
      rfl

end LeanCanny.Algebra.CoordinatePowerSubstitution
