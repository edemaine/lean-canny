/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.BivariateSpecializationMass
public import LeanCanny.CountingHierarchy.CriticalFeasibility

/-! # Short exponents for a discriminant-avoiding specialization

The integers themselves may have exponentially many bits. Their displayed
exponents use a fixed number of arithmetic operations on the source bounds.
-/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra

/-- Exponent of the value cutoff. -/
@[expose] def criticalValueCutoffExponent (H : ℕ) : ℕ := H + 2

/-- Exponent of the deformation parameter, avoiding both the derivative
 resultant and the value section. -/
@[expose] def criticalParameterExponent (D H : ℕ) : ℕ :=
  derivativeResultantMassExponent D H + H + D * criticalValueCutoffExponent H + 2

/-- Casting a coefficient bound and adding one costs one additional bit. -/
theorem cast_add_one_le_pow {m b c : ℕ} (hm : m ≤ 2 ^ b) (hc : b + 1 ≤ c) :
    (m : ℝ) + 1 ≤ (2 : ℝ) ^ c := by
  have h : m + 1 ≤ 2 ^ c := by
    calc
      _ ≤ 2 ^ b * 2 := by have := Nat.one_le_two_pow (n := b); omega
      _ = 2 ^ (b + 1) := (pow_succ 2 b).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hc
  exact_mod_cast h

theorem large_value_cutoff (Q : Polynomial (Polynomial ℤ)) (H : ℕ)
    (hH : NestedMass.mass Q ≤ 2 ^ H) :
    (coefficientMass (Bivariate.swap Q).leadingCoeff : ℝ) + 1 ≤
      (((2 : ℤ) ^ criticalValueCutoffExponent H : ℤ) : ℝ) := by
  have hm : coefficientMass (Bivariate.swap Q).leadingCoeff ≤ 2 ^ H :=
    ((NestedMass.coeff_le (Bivariate.swap Q) _).trans_eq (NestedMass.swap Q)).trans hH
  simpa only [Int.cast_pow, Int.cast_ofNat] using
    cast_add_one_le_pow hm (show H + 1 ≤ criticalValueCutoffExponent H by unfold criticalValueCutoffExponent; omega)

theorem large_parameter_avoids_value_section (Q : Polynomial (Polynomial ℤ)) (D H : ℕ)
    (hD : Q.natDegree ≤ D) (hH : NestedMass.mass Q ≤ 2 ^ H) :
    (coefficientMass (integerValueSection (Bivariate.swap Q)
      ((2 : ℤ) ^ criticalValueCutoffExponent H)) : ℝ) + 1 ≤
        (2 : ℝ) ^ criticalParameterExponent D H := by
  have habs : ((2 : ℤ) ^ criticalValueCutoffExponent H).natAbs =
      2 ^ criticalValueCutoffExponent H := by rw [Int.natAbs_pow]; rfl
  have hm := integerValueSection_mass_le Q D hD
    ((2 : ℤ) ^ criticalValueCutoffExponent H) (by rw [habs]; exact Nat.one_le_two_pow)
  have hb : coefficientMass (integerValueSection (Bivariate.swap Q)
      ((2 : ℤ) ^ criticalValueCutoffExponent H)) ≤ 2 ^ (H + D * criticalValueCutoffExponent H) := by
    apply hm.trans
    rw [habs]
    exact (Nat.mul_le_mul_right _ hH).trans_eq (by rw [← pow_mul, ← pow_add, Nat.mul_comm D])
  exact cast_add_one_le_pow hb (by unfold criticalParameterExponent; omega)

theorem large_parameter_avoids_derivative_resultant (Q : Polynomial (Polynomial ℤ)) (D H : ℕ)
    (hD : Q.natDegree ≤ D) (hH : NestedMass.mass Q ≤ 2 ^ H) :
    (coefficientMass (Q.resultant Q.derivative) : ℝ) + 1 ≤
      (2 : ℝ) ^ criticalParameterExponent D H :=
  cast_add_one_le_pow (derivative_resultant_mass_le Q D H hD hH)
    (by unfold criticalParameterExponent; omega)

/-- The finite feasibility test with cutoffs specified only by the short
 degree and log-mass bounds of the constructed critical polynomial. -/
theorem real_zero_iff_root_at_power_specialization {n : ℕ}
    (d : ℕ) (hd : 1 ≤ d) (he : Even (d + 2))
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hFn : ∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x (F.map (Int.castRingHom ℝ)))
    (H : ℕ) (hH : NestedMass.mass (parametricCriticalValue d F hF) ≤ 2 ^ H) :
    (∃ x : Fin n → ℝ, MvPolynomial.eval x (F.map (Int.castRingHom ℝ)) = 0) ↔
      ∃ η : ℝ, η < (2 : ℝ) ^ criticalValueCutoffExponent H ∧
        ((parametricCriticalValue d F hF).map
          (parameterEvaluation ((2 : ℝ) ^ criticalParameterExponent ((d + 1) ^ n) H))).IsRoot η := by
  have hD : (parametricCriticalValue d F hF).natDegree ≤ (d + 1) ^ n :=
    (parametricCriticalValue_natDegree d F hF).le
  simpa only [Int.cast_pow, Int.cast_ofNat] using
    real_zero_iff_specialized_critical_root d hd he F hF hFn
      ((2 : ℤ) ^ criticalValueCutoffExponent H)
      (large_value_cutoff _ H hH)
      ((2 : ℝ) ^ criticalParameterExponent ((d + 1) ^ n) H)
      (large_parameter_avoids_value_section _ _ H hD hH)
      (large_parameter_avoids_derivative_resultant _ _ H hD hH)

end LeanCanny.CountingHierarchy
