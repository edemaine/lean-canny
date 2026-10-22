/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CriticalValueAnnihilator
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Integer annihilants of the real critical values of rational polynomials

The gradient-ideal annihilator remains valid over extension fields. Clearing
its rational coefficients yields one nonzero integer polynomial vanishing on
all real critical values. This existence argument supplies no source-size
bound on its degree or coefficient mass.
-/

@[expose] public section

namespace LeanCanny.Algebra.CriticalValueAnnihilator
open MvPolynomial

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

theorem eval_annihilator_extension (p : MvPolynomial ι K) (q : Polynomial K)
    (hq : Polynomial.aeval p q ∈ (gradientIdeal p).radical) (x : ι → L)
    (hx : ∀ i, MvPolynomial.aeval x (pderiv i p) = 0) :
    Polynomial.aeval (MvPolynomial.aeval x p) q = 0 := by
  have hI : gradientIdeal p ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hx i
  obtain ⟨n, hn⟩ := hq
  have he := hI hn
  change MvPolynomial.aeval x ((Polynomial.aeval p q) ^ n) = 0 at he
  rw [map_pow, ← Polynomial.aeval_algHom_apply] at he
  exact eq_zero_of_pow_eq_zero he

theorem exists_integer_real_annihilator [Fintype ι] (p : MvPolynomial ι ℚ) :
    ∃ q : Polynomial ℤ, q ≠ 0 ∧ ∀ x : ι → ℝ,
      (∀ i, MvPolynomial.aeval x (pderiv i p) = 0) →
        Polynomial.aeval (MvPolynomial.aeval x p) q = 0 := by
  obtain ⟨r, hr, hm⟩ := exists_annihilator p
  obtain ⟨m, hmem, he⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) r
  let q := IsLocalization.integerNormalization (nonZeroDivisors ℤ) r
  have hscale : q.map (algebraMap ℤ ℚ) = Polynomial.C (m : ℚ) * r := by
    rw [← IsScalarTower.algebraMap_smul ℚ m r, Polynomial.smul_eq_C_mul] at he
    exact he
  have hmn : (m : ℤ) ≠ 0 := nonZeroDivisors.ne_zero hmem
  have hq : q ≠ 0 := by
    intro hz
    have h := hscale
    rw [hz, Polynomial.map_zero] at h
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr (Int.cast_ne_zero.mpr hmn)) hr) h.symm
  refine ⟨q, hq, ?_⟩
  intro x hx
  have hz := eval_annihilator_extension p r hm x hx
  calc
    Polynomial.aeval (MvPolynomial.aeval x p) q =
        Polynomial.aeval (MvPolynomial.aeval x p) (q.map (algebraMap ℤ ℚ)) :=
      Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq ℤ ℚ ℝ).symm q _
    _ = 0 := by rw [hscale, map_mul, hz, mul_zero]

end LeanCanny.Algebra.CriticalValueAnnihilator
