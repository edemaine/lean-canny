/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GroupedPolynomialDivisors
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Polynomial cancellation from denominator families omitting input groups

A reduced fraction's denominator divides every denominator representing
that fraction. Consequently normalized polynomial denominator families
omitting each coefficient group force their common fraction to be a
polynomial. Cross-multiplication identities suffice to construct the common
polynomial quotient.
-/

@[expose] public section

namespace LeanCanny.Algebra.GroupedDenominatorCancellation
open scoped Classical
variable {A K ι : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  [Field K] [Algebra A K] [IsFractionRing A K]

theorem den_dvd_of_mul_eq (x : K) (a b : A) (h : x * algebraMap A K b = algebraMap A K a) :
    (IsFractionRing.den A x : A) ∣ b := by
  have hn : x * algebraMap A K (IsFractionRing.den A x) = algebraMap A K (IsFractionRing.num A x) :=
    (IsFractionRing.num_mul_den_eq_num_iff_eq (x := x) (y := x)).mpr rfl
  have hc : IsFractionRing.num A x * b = a * (IsFractionRing.den A x : A) := by
    apply FaithfulSMul.algebraMap_injective A K
    rw [map_mul, map_mul]
    calc
      _ = (x * algebraMap A K (IsFractionRing.den A x)) * algebraMap A K b := by rw [hn]
      _ = (x * algebraMap A K b) * algebraMap A K (IsFractionRing.den A x) := by ring
      _ = _ := by rw [h]
  apply (IsFractionRing.num_den_reduced A x).symm.dvd_of_dvd_mul_left
  exact ⟨a, hc.trans (mul_comm _ _)⟩

theorem isInteger_of_denominators (x : K) (a b : ι → A)
    (h : ∀ i, x * algebraMap A K (b i) = algebraMap A K (a i))
    (hcommon : ∀ g : A, (∀ i, g ∣ b i) → IsUnit g) : IsLocalization.IsInteger A x :=
  IsFractionRing.isInteger_of_isUnit_den
    (hcommon (IsFractionRing.den A x) (fun i => den_dvd_of_mul_eq x (a i) (b i) (h i)))

variable {R σ : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [Nonempty ι]

theorem isPolynomial_of_omitted_groups
    {F : Type*} [Field F] [Algebra (MvPolynomial σ R) F] [IsFractionRing (MvPolynomial σ R) F]
    (owner : σ → ι) (a b : ι → MvPolynomial σ R)
    (homit : ∀ i v, v ∈ (b i).vars → owner v ≠ i) (point : σ → R)
    (hnorm : ∀ i, MvPolynomial.eval point (b i) = 1) (x : F)
    (h : ∀ i, x * algebraMap (MvPolynomial σ R) F (b i) = algebraMap (MvPolynomial σ R) F (a i)) :
    IsLocalization.IsInteger (MvPolynomial σ R) x :=
  isInteger_of_denominators x a b h
    (GroupedPolynomialDivisors.isUnit_common_divisor owner b homit point hnorm)

theorem exists_polynomial_quotient (owner : σ → ι) (a b : ι → MvPolynomial σ R)
    (homit : ∀ i v, v ∈ (b i).vars → owner v ≠ i) (point : σ → R)
    (hnorm : ∀ i, MvPolynomial.eval point (b i) = 1)
    (hcross : ∀ i j, a i * b j = a j * b i) :
    ∃ q : MvPolynomial σ R, ∀ i, a i = b i * q := by
  let P := MvPolynomial σ R
  let F := FractionRing P
  let i₀ : ι := Classical.arbitrary ι
  have hb : b i₀ ≠ 0 := by
    intro hz
    have h := hnorm i₀
    rw [hz, map_zero] at h
    exact zero_ne_one h
  have hbF : algebraMap P F (b i₀) ≠ 0 :=
    by simpa only [map_zero] using (FaithfulSMul.algebraMap_injective P F).ne hb
  let x : F := algebraMap P F (a i₀) / algebraMap P F (b i₀)
  have hrep (i : ι) : x * algebraMap P F (b i) = algebraMap P F (a i) := by
    change (algebraMap P F (a i₀) / algebraMap P F (b i₀)) * algebraMap P F (b i) = algebraMap P F (a i)
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hbF).mpr
    simpa only [map_mul] using congrArg (algebraMap P F) (hcross i₀ i)
  obtain ⟨q, hq⟩ := isPolynomial_of_omitted_groups owner a b homit point hnorm x hrep
  refine ⟨q, fun i => ?_⟩
  apply FaithfulSMul.algebraMap_injective P F
  rw [map_mul, hq]
  exact (hrep i).symm.trans (mul_comm _ _)

end LeanCanny.Algebra.GroupedDenominatorCancellation
