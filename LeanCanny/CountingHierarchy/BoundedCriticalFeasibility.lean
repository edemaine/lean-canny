/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParametricCriticalBounds
public import LeanCanny.CountingHierarchy.LargeSpecializationBounds

/-! # A source-bounded integer univariate reduction of real feasibility -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra

variable {n : ℕ}

theorem parameterEvaluation_intCast {K : Type*} [CommRing K] (u : ℤ) :
    parameterEvaluation (u : K) = (Int.castRingHom K).comp (Polynomial.evalRingHom u) := by
  ext <;> simp [parameterEvaluation]

/-- An integer polynomial, obtained by evaluating the parameter at a power
 of two specified by a short exponent. -/
@[expose] noncomputable def powerCriticalValue (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (s : ℕ) : Polynomial ℤ :=
  (parametricCriticalValue d F hF).map (Polynomial.evalRingHom ((2 : ℤ) ^ s))

theorem powerCriticalValue_map {K : Type*} [CommRing K] (d : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (s : ℕ) :
    (powerCriticalValue d F hF s).map (Int.castRingHom K) =
      (parametricCriticalValue d F hF).map (parameterEvaluation ((2 : K) ^ s)) := by
  rw [powerCriticalValue, Polynomial.map_map, ← parameterEvaluation_intCast]
  simp only [Int.cast_pow, Int.cast_ofNat]

theorem powerCriticalValue_monic (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (s : ℕ) : (powerCriticalValue d F hF s).Monic :=
  (parametricCriticalValue_monic d F hF).map _

theorem powerCriticalValue_natDegree (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (s : ℕ) :
    (powerCriticalValue d F hF s).natDegree = (d + 1) ^ n := by
  rw [powerCriticalValue, (parametricCriticalValue_monic d F hF).natDegree_map,
    parametricCriticalValue_natDegree]

theorem powerCriticalValue_mass_le (d : ℕ) (hd : 1 ≤ d) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hM : MvMass.mass F ≤ 2 ^ b) (s : ℕ) :
    coefficientMass (powerCriticalValue d F hF s) ≤
      2 ^ (criticalValueMassExponent n d b + s * criticalValueParameterDegreeBound n d) := by
  have habs : ((2 : ℤ) ^ s).natAbs = 2 ^ s := by rw [Int.natAbs_pow]; rfl
  have hb := coefficientMass_map_eval_le (parametricCriticalValue d F hF)
    (criticalValueParameterDegreeBound n d) (parametricCriticalValue_parameterDegree_le d hd F hF)
    ((2 : ℤ) ^ s) (by rw [habs]; exact Nat.one_le_two_pow)
  apply hb.trans
  rw [habs]
  exact (Nat.mul_le_mul_right _ (parametricCriticalValue_mass_le d hd b F hF hM)).trans_eq
    (by rw [← pow_mul, ← pow_add])

/-- Real feasibility reduces to a root of a monic integer polynomial of
 degree `(d+1)^n`, with source-derived specialization and value exponents. -/
theorem real_zero_iff_source_bounded_critical_root (d : ℕ) (hd : 1 ≤ d) (he : Even (d + 2))
    (b : ℕ) (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hM : MvMass.mass F ≤ 2 ^ b)
    (hFn : ∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x (F.map (Int.castRingHom ℝ))) :
    (∃ x : Fin n → ℝ, MvPolynomial.eval x (F.map (Int.castRingHom ℝ)) = 0) ↔
      ∃ η : ℝ, η < (2 : ℝ) ^ criticalValueCutoffExponent (criticalValueMassExponent n d b) ∧
        ((powerCriticalValue d F hF
          (criticalParameterExponent ((d + 1) ^ n) (criticalValueMassExponent n d b))).map
            (Int.castRingHom ℝ)).IsRoot η := by
  rw [powerCriticalValue_map]
  exact real_zero_iff_root_at_power_specialization d hd he F hF hFn _
    (parametricCriticalValue_mass_le d hd b F hF hM)

/-- The chosen source-bounded specialization has no repeated roots. -/
theorem source_bounded_criticalValue_separable (d : ℕ) (hd : 1 ≤ d) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hM : MvMass.mass F ≤ 2 ^ b) :
    ((powerCriticalValue d F hF
      (criticalParameterExponent ((d + 1) ^ n) (criticalValueMassExponent n d b))).map
        (Int.castRingHom ℝ)).Separable := by
  rw [powerCriticalValue_map]
  apply criticalValue_separable_of_large_parameter d hd F hF
  rw [abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
  exact large_parameter_avoids_derivative_resultant _ _ _
    (parametricCriticalValue_natDegree d F hF).le (parametricCriticalValue_mass_le d hd b F hF hM)

end LeanCanny.CountingHierarchy
