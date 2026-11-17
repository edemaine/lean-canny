/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CriticalPolynomialMap
public import LeanCanny.CountingHierarchy.QuotientMultiplicationMatrix
public import LeanCanny.CountingHierarchy.SeparatedCriticalValues

/-! # The integer critical-value polynomial with an indeterminate parameter -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial PurePowerResidue
open scoped Classical

variable {n : ℕ}

@[expose] noncomputable def parameterCenters (d : ℕ) (i : Fin n) : Polynomial ℤ :=
  Polynomial.C (separatedCenters (d + 1) i : ℤ)

@[expose] noncomputable def parameterLower (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (i : Fin n) : MvPolynomial (Fin n) (Polynomial ℤ) :=
  criticalLower (d + 1) (parameterCenters d) Polynomial.X (F.map Polynomial.C) i

@[expose] noncomputable def parameterObjective (d : ℕ) (F : MvPolynomial (Fin n) ℤ) :
    MvPolynomial (Fin n) (Polynomial ℤ) :=
  deformedPolynomial (d + 1) (parameterCenters d) Polynomial.X (F.map Polynomial.C)

theorem parameterLower_degree (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (i : Fin n) :
    (parameterLower d F i).totalDegree < d + 1 :=
  criticalLower_degree (d + 1) (by omega) _ _ _
    ((map_degree_le Polynomial.C F).trans hF) i

/-- The outer variable is the critical value and the coefficient-ring
 variable is the deformation parameter. Both coefficient rings are integral. -/
@[expose] noncomputable def parametricCriticalValue (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) : Polynomial (Polynomial ℤ) :=
  (multiplicationMatrix (by omega : 1 ≤ d + 1) (parameterLower d F)
    (parameterLower_degree d F hF) (parameterObjective d F)).charpoly

theorem parametricCriticalValue_monic (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) : (parametricCriticalValue d F hF).Monic :=
  Matrix.charpoly_monic _

theorem parametricCriticalValue_natDegree (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) : (parametricCriticalValue d F hF).natDegree = (d + 1) ^ n := by
  rw [parametricCriticalValue, Matrix.charpoly_natDegree_eq_dim, card_normalIndex]

/-- Evaluate the deformation parameter while casting the original integers. -/
@[expose] noncomputable def parameterEvaluation {K : Type*} [CommRing K] (u : K) :
    Polynomial ℤ →+* K := Polynomial.eval₂RingHom (Int.castRingHom K) u

theorem parameterEvaluation_C {K : Type*} [CommRing K] (u : K) (z : ℤ) :
    parameterEvaluation u (Polynomial.C z) = z := Polynomial.eval₂_C _ _

theorem parameterEvaluation_X {K : Type*} [CommRing K] (u : K) :
    parameterEvaluation u Polynomial.X = u := Polynomial.eval₂_X _ _

theorem map_parameter_integer_polynomial {K : Type*} [CommRing K] (u : K)
    (F : MvPolynomial (Fin n) ℤ) :
    (F.map Polynomial.C).map (parameterEvaluation u) = F.map (Int.castRingHom K) := by
  have hc : (parameterEvaluation u).comp Polynomial.C = Int.castRingHom K := by
    ext z
    exact parameterEvaluation_C u z
  rw [map_map, hc]

theorem parameterLower_map {K : Type*} [CommRing K] (d : ℕ) (u : K)
    (F : MvPolynomial (Fin n) ℤ) (i : Fin n) :
    (parameterLower d F i).map (parameterEvaluation u) =
      criticalLower (d + 1) (fun j => (separatedCenters (d + 1) j : K)) u
        (F.map (Int.castRingHom K)) i := by
  rw [parameterLower, criticalLower_map, parameterEvaluation_X, map_parameter_integer_polynomial]
  simp only [parameterCenters, parameterEvaluation_C, Int.cast_natCast]

theorem parameterObjective_map {K : Type*} [CommRing K] (d : ℕ) (u : K)
    (F : MvPolynomial (Fin n) ℤ) :
    (parameterObjective d F).map (parameterEvaluation u) =
      deformedPolynomial (d + 1) (fun j => (separatedCenters (d + 1) j : K)) u
        (F.map (Int.castRingHom K)) := by
  rw [parameterObjective, deformedPolynomial_map, parameterEvaluation_X, map_parameter_integer_polynomial]
  simp only [parameterCenters, parameterEvaluation_C, Int.cast_natCast]

end LeanCanny.CountingHierarchy
