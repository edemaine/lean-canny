/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.BoundedCriticalFeasibility
public import LeanCanny.CountingHierarchy.QuotientCharacteristicRingSpecialization
public import LeanCanny.CountingHierarchy.QuotientRealSpectralProduct

/-! # The specialized integer polynomial is the integer quotient characteristic polynomial -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial MvPolynomial PurePowerResidue

variable {n : ℕ}

theorem parametricCriticalValue_map_integer (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (u : ℤ) :
    (parametricCriticalValue d F hF).map (Polynomial.evalRingHom u) =
      (multiplicationMatrix (by omega : 1 ≤ d + 1)
        (criticalLower (d + 1) (fun i => (separatedCenters (d + 1) i : ℤ)) u F)
        (criticalLower_degree (d + 1) (by omega) _ _ F hF)
        (deformedPolynomial (d + 1) (fun i => (separatedCenters (d + 1) i : ℤ)) u F)).charpoly := by
  have hr (i : Fin n) : (parameterLower d F i).totalDegree ≤ d := by
    have := parameterLower_degree d F hF i
    omega
  have h := multiplicationMatrix_charpoly_map_charZero (parameterEvaluation u) d hd
    (parameterLower d F) hr (parameterObjective d F)
  have hInt : Int.castRingHom ℤ = RingHom.id ℤ := by ext z; rfl
  have hφ : parameterEvaluation u = Polynomial.evalRingHom u := by
    ext <;> simp [parameterEvaluation]
  have hlow : (fun i => (parameterLower d F i).map (parameterEvaluation u)) =
      criticalLower (d + 1) (fun i => (separatedCenters (d + 1) i : ℤ)) u F := by
    funext i
    simpa only [hInt, MvPolynomial.map_id, Int.cast_id] using parameterLower_map d u F i
  have hv : (parameterObjective d F).map (parameterEvaluation u) =
      deformedPolynomial (d + 1) (fun i => (separatedCenters (d + 1) i : ℤ)) u F := by
    simpa only [hInt, MvPolynomial.map_id, Int.cast_id] using parameterObjective_map d u F
  have hc := h.trans (multiplicationMatrix_charpoly_congr (by omega : 1 ≤ d + 1)
    _ _ _ (criticalLower_degree (d + 1) (by omega) _ _ F hF) _ _ hlow hv)
  simpa only [hφ, parametricCriticalValue] using hc

/-- The source-bounded integer specialization itself is separable after
 casting to the complex splitting field. -/
theorem source_bounded_criticalValue_separable_complex (d : ℕ) (hd : 1 ≤ d) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hM : LeanCanny.Algebra.MvMass.mass F ≤ 2 ^ b) :
    ((powerCriticalValue d F hF
      (criticalParameterExponent ((d + 1) ^ n) (criticalValueMassExponent n d b))).map
        (Int.castRingHom ℂ)).Separable := by
  rw [← integer_real_complex_polynomial_map]
  exact (Polynomial.separable_map (algebraMap ℝ ℂ)).mpr
    (source_bounded_criticalValue_separable d hd b F hF hM)

end LeanCanny.CountingHierarchy
