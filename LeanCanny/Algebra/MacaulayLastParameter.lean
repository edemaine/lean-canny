/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayExtraneousLast
public import LeanCanny.Algebra.CharacteristicQuotientDegree

/-! # Polynomiality in a parameter occurring only in the last input

Input coefficients are polynomials in u; the characteristic parameter is s.
Swapping these variables and embedding K[s] in K(s) gives matrices over
K(s)[u]. The extraneous determinant is a nonzero constant in u when only the
last input varies. The determinant quotient is consequently a polynomial in u.
Polynomiality in s and the multivariate resultant identity remain separate.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayLastParameter
open Macaulay
open scoped Classical
variable {n : ℕ} {K : Type*} [Field K]

noncomputable def parameterMap : Polynomial (Polynomial K) →+* Polynomial (RatFunc K) :=
  (Polynomial.mapRingHom (algebraMap (Polynomial K) (RatFunc K))).comp Polynomial.Bivariate.swap.toRingHom

theorem parameterMap_injective : Function.Injective (parameterMap (K := K)) :=
  (Polynomial.map_injective _ (RatFunc.algebraMap_injective K)).comp Polynomial.Bivariate.swap.injective

noncomputable def swapExtension : RatFunc (Polynomial K) →+* RatFunc (RatFunc K) :=
  RatFunc.mapRingHom (parameterMap (K := K))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ parameterMap_injective)

theorem swapExtension_injective : Function.Injective (swapExtension (K := K)) :=
  RatFunc.map_injective (parameterMap (K := K))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ parameterMap_injective) parameterMap_injective

theorem swapExtension_mk (p q : Polynomial (Polynomial K)) :
    swapExtension (RatFunc.mk p q) = RatFunc.mk (parameterMap p) (parameterMap q) := by
  rw [RatFunc.mk_eq_div, RatFunc.mk_eq_div]
  exact RatFunc.map_apply_div (parameterMap (K := K))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ parameterMap_injective) p q

theorem parameterMap_C_C (a : K) : parameterMap (Polynomial.C (Polynomial.C a)) =
    Polynomial.C (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a)) := by
  change (Polynomial.Bivariate.swap (Polynomial.C (Polynomial.C a))).map _ = _
  rw [Polynomial.Bivariate.swap_C_C, Polynomial.map_C]

theorem parameterMap_X : parameterMap (Polynomial.X : Polynomial (Polynomial K)) =
    Polynomial.C (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) := by
  change (Polynomial.Bivariate.swap (Polynomial.X : Polynomial (Polynomial K))).map _ = _
  rw [Polynomial.Bivariate.swap_Y, Polynomial.map_C]

noncomputable def system (p : Fin n → MvPolynomial (Fin n) (Polynomial K)) (d : Fin n → ℕ) :=
  fun i => (subtractiveSystem p d i).map (parameterMap (K := K))

noncomputable def constantMap : Polynomial K →+* Polynomial (RatFunc K) :=
  Polynomial.C.comp (algebraMap (Polynomial K) (RatFunc K))

theorem system_eq_constant (p : Fin n → MvPolynomial (Fin n) (Polynomial K))
    (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (i : Fin n)
    (hi : p i = (q i).map Polynomial.C) :
    system p d i = (subtractiveSystem q d i).map (constantMap (K := K)) := by
  unfold system subtractiveSystem
  rw [hi]
  ext e
  by_cases he : Finsupp.single i (d i) = e <;>
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial,
      he, ite_true, ite_false, map_sub, map_zero, parameterMap_C_C, parameterMap_X, constantMap, RingHom.comp_apply]

noncomputable def denominatorValue (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (AffineCharacteristic.subtractiveMatrix (extraneousMinor q d W)).det

theorem denominatorValue_ne_zero (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ) :
    denominatorValue q d W ≠ 0 :=
  RatFunc.algebraMap_ne_zero (AffineCharacteristic.subtractive_det_ne_zero (extraneousMinor q d W))

noncomputable def denominator (p : Fin n → MvPolynomial (Fin n) (Polynomial K)) (d : Fin n → ℕ) (W : ℕ) :
    Polynomial (RatFunc K) := (extraneousMinor (system p d) d W).det

theorem denominator_constant (p : Fin n → MvPolynomial (Fin n) (Polynomial K))
    (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ)
    (last : Fin n) (hlast : ∀ j, j ≤ last) (hpq : ∀ i, i ≠ last → p i = (q i).map Polynomial.C) :
    denominator p d W = Polynomial.C (denominatorValue q d W) := by
  have he := extraneousMinor_eq_off_last (system p d)
    (fun i => (subtractiveSystem q d i).map (constantMap (K := K))) d W last hlast
    (fun i hi => system_eq_constant p q d i (hpq i hi))
  have hm := det_extraneousMinor_map (constantMap (K := K)) (subtractiveSystem q d) d W
  rw [extraneousMinor_subtractiveSystem] at hm
  unfold denominator
  rw [he]
  exact hm.symm

noncomputable def numerator (p : Fin n → MvPolynomial (Fin n) (Polynomial K)) (d : Fin n → ℕ) (W : ℕ) :
    Polynomial (RatFunc K) := (activeMinor (system p d) d W).det

theorem numerator_eq_parameterMap (p : Fin n → MvPolynomial (Fin n) (Polynomial K)) (d : Fin n → ℕ) (W : ℕ) :
    numerator p d W = parameterMap (activeCharacteristic p d W) := by
  have h := det_activeMinor_map (parameterMap (K := K)) (subtractiveSystem p d) d W
  rw [activeMinor_subtractiveSystem] at h
  exact h.symm

theorem denominator_eq_parameterMap (p : Fin n → MvPolynomial (Fin n) (Polynomial K)) (d : Fin n → ℕ) (W : ℕ) :
    denominator p d W = parameterMap (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det := by
  have h := det_extraneousMinor_map (parameterMap (K := K)) (subtractiveSystem p d) d W
  rw [extraneousMinor_subtractiveSystem] at h
  exact h.symm

theorem numerator_ne_zero (p : Fin n → MvPolynomial (Fin n) (Polynomial K)) (d : Fin n → ℕ) (W : ℕ) :
    numerator p d W ≠ 0 := by
  have hn := AffineCharacteristic.subtractive_det_ne_zero (activeMinor p d W)
  rw [← activeMinor_subtractiveSystem] at hn
  have hm := det_activeMinor_map (parameterMap (K := K)) (subtractiveSystem p d) d W
  change _ = numerator p d W at hm
  rw [← hm]
  exact (map_ne_zero_iff _ parameterMap_injective).mpr hn

noncomputable def value (p : Fin n → MvPolynomial (Fin n) (Polynomial K)) (d : Fin n → ℕ) (W : ℕ) :
    RatFunc (RatFunc K) := RatFunc.mk (numerator p d W) (denominator p d W)

theorem value_eq_extension (p : Fin n → MvPolynomial (Fin n) (Polynomial K)) (d : Fin n → ℕ) (W : ℕ) :
    value p d W = swapExtension (RatFunc.mk (activeCharacteristic p d W)
      (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det) := by
  rw [value, numerator_eq_parameterMap, denominator_eq_parameterMap, swapExtension_mk]

noncomputable def polynomial (p : Fin n → MvPolynomial (Fin n) (Polynomial K))
    (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ) : Polynomial (RatFunc K) :=
  Polynomial.C (denominatorValue q d W)⁻¹ * numerator p d W

theorem polynomial_ne_zero (p : Fin n → MvPolynomial (Fin n) (Polynomial K))
    (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ) : polynomial p q d W ≠ 0 := by
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr (inv_ne_zero (denominatorValue_ne_zero q d W))) (numerator_ne_zero p d W)

theorem polynomial_mul_denominator (p : Fin n → MvPolynomial (Fin n) (Polynomial K))
    (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ) :
    polynomial p q d W * Polynomial.C (denominatorValue q d W) = numerator p d W := by
  unfold polynomial
  calc
    _ = (Polynomial.C (denominatorValue q d W)⁻¹ * Polynomial.C (denominatorValue q d W)) * numerator p d W := by ring
    _ = _ := by rw [← map_mul, inv_mul_cancel₀ (denominatorValue_ne_zero q d W), map_one, one_mul]

theorem value_eq_polynomial (p : Fin n → MvPolynomial (Fin n) (Polynomial K))
    (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ)
    (last : Fin n) (hlast : ∀ j, j ≤ last) (hpq : ∀ i, i ≠ last → p i = (q i).map Polynomial.C) :
    value p d W = algebraMap (Polynomial (RatFunc K)) (RatFunc (RatFunc K)) (polynomial p q d W) := by
  rw [value, denominator_constant p q d W last hlast hpq, RatFunc.mk_eq_div]
  have hn : Polynomial.C (denominatorValue q d W) ≠ (0 : Polynomial (RatFunc K)) :=
    Polynomial.C_ne_zero.mpr (denominatorValue_ne_zero q d W)
  apply (div_eq_iff (RatFunc.algebraMap_ne_zero hn)).mpr
  rw [← map_mul, polynomial_mul_denominator]

theorem exists_nonzero_polynomial (p : Fin n → MvPolynomial (Fin n) (Polynomial K))
    (q : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ)
    (last : Fin n) (hlast : ∀ j, j ≤ last) (hpq : ∀ i, i ≠ last → p i = (q i).map Polynomial.C) :
    ∃ r : Polynomial (RatFunc K), r ≠ 0 ∧
      swapExtension (RatFunc.mk (activeCharacteristic p d W)
        (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det) = algebraMap _ _ r := by
  refine ⟨polynomial p q d W, polynomial_ne_zero p q d W, ?_⟩
  rw [← value_eq_extension]
  exact value_eq_polynomial p q d W last hlast hpq

end LeanCanny.Algebra.MacaulayLastParameter
