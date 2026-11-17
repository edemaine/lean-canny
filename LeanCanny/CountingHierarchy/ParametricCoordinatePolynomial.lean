/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParametricCriticalSpecialization
public import LeanCanny.CountingHierarchy.QuotientEvaluation

/-! # Coordinate characteristic polynomials for the zero-center deformation -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial PurePowerResidue
open scoped Classical

variable {n : ℕ}

noncomputable def coordinateParameterLower (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (i : Fin n) : MvPolynomial (Fin n) (Polynomial ℤ) :=
  criticalLower (d + 1) (fun _ => 0) Polynomial.X (F.map Polynomial.C) i

theorem coordinateParameterLower_degree (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (i : Fin n) : (coordinateParameterLower d F i).totalDegree < d + 1 :=
  criticalLower_degree (d + 1) (by omega) _ _ _ ((map_degree_le Polynomial.C F).trans hF) i

noncomputable def parametricCoordinatePolynomial (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (i : Fin n) : Polynomial (Polynomial ℤ) :=
  (multiplicationMatrix (by omega : 1 ≤ d + 1) (coordinateParameterLower d F)
    (coordinateParameterLower_degree d F hF) (MvPolynomial.X i)).charpoly

theorem parametricCoordinatePolynomial_monic (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (i : Fin n) : (parametricCoordinatePolynomial d F hF i).Monic :=
  Matrix.charpoly_monic _

theorem parametricCoordinatePolynomial_natDegree (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (i : Fin n) :
    (parametricCoordinatePolynomial d F hF i).natDegree = (d + 1) ^ n := by
  rw [parametricCoordinatePolynomial, Matrix.charpoly_natDegree_eq_dim, card_normalIndex]

theorem coordinateParameterLower_map {K : Type*} [CommRing K] (d : ℕ) (u : K)
    (F : MvPolynomial (Fin n) ℤ) (i : Fin n) :
    (coordinateParameterLower d F i).map (parameterEvaluation u) =
      criticalLower (d + 1) (fun _ => 0) u (F.map (Int.castRingHom K)) i := by
  rw [coordinateParameterLower, criticalLower_map, parameterEvaluation_X, map_parameter_integer_polynomial]
  simp only [map_zero]

theorem parametricCoordinatePolynomial_map {K : Type*} [Field K] (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (i : Fin n) (u : K)
    (hK : ∀ j, 1 ≤ j → j ≤ (d + 1) ^ n → (j : K) ≠ 0) :
    (parametricCoordinatePolynomial d F hF i).map (parameterEvaluation u) =
      (multiplicationMatrix (by omega : 1 ≤ d + 1)
        (criticalLower (d + 1) (fun _ => 0) u (F.map (Int.castRingHom K)))
        (criticalLower_degree (d + 1) (by omega) _ _ _ ((map_degree_le _ F).trans hF)) (MvPolynomial.X i)).charpoly := by
  have hr (j : Fin n) : (coordinateParameterLower d F j).totalDegree ≤ d := by
    have := coordinateParameterLower_degree d F hF j
    omega
  have h := multiplicationMatrix_charpoly_map (parameterEvaluation u) d hd
    (coordinateParameterLower d F) hr (MvPolynomial.X i) hK
  have hlow : (fun j : Fin n => (coordinateParameterLower d F j).map (parameterEvaluation u)) =
      criticalLower (d + 1) (fun _ => 0) u (F.map (Int.castRingHom K)) :=
    funext (coordinateParameterLower_map d u F)
  exact h.trans (multiplicationMatrix_charpoly_congr (ell := d + 1) (by omega) _ _ _ _ _ _
    hlow (MvPolynomial.map_X _ _))

/-- At every common zero, each coordinate is a root of its actual specialized
characteristic polynomial. Multiple eigenvalues require no special treatment. -/
theorem parametricCoordinatePolynomial_root (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (i : Fin n) (u : ℝ)
    (x : Fin n → ℝ) (hx : ∀ j, MvPolynomial.aeval x
      (criticalLower (d + 1) (fun _ => 0) u (F.map (Int.castRingHom ℝ)) j) = x j ^ (d + 1)) :
    ((parametricCoordinatePolynomial d F hF i).map (parameterEvaluation u)).eval (x i) = 0 := by
  rw [parametricCoordinatePolynomial_map d hd F hF i u (by
    intro j hj _
    exact_mod_cast (by omega : j ≠ 0))]
  have h := charpoly_eval_at_common_zero (by omega : 1 ≤ d + 1) _
    (criticalLower_degree (d + 1) (by omega) _ _ _ ((map_degree_le _ F).trans hF)) (MvPolynomial.X i) x hx
  simpa only [MvPolynomial.aeval_X, Polynomial.coe_aeval_eq_eval] using h

end LeanCanny.CountingHierarchy
