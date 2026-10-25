/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.UniformAffineCoordinates
public import LeanCanny.Algebra.ProjectionCriticalBounds

/-! # Bounded coordinate certificates for spatial critical slice families

The actual critical equations retain the original spatial and parameter
degree allowances. Their coefficient-mass increase depends explicitly on the
degree and integer direction. Applying the concrete affine eliminant gives
bounded coordinate equations and a bounded-degree specialization factor.
The direction and the separate regularity factor still require input bounds.
-/

@[expose] public section

namespace LeanCanny.Geometry.BoundedCriticalCoordinates
open LeanCanny.Algebra Polynomial

variable {n : ℕ}

theorem exists_bounded (q : MvPolynomial (Fin n) (Polynomial ℤ)) (base : Fin n)
    (v : Fin n → ℕ) (D U E b : ℕ) (hD : q.totalDegree ≤ D) (hU : ∀ i, v i ≤ U)
    (hdegree : ∀ e, (q.coeff e).natDegree ≤ E)
    (hmass : ∀ e, coefficientMass (q.coeff e) ≤ 2 ^ b) :
    let d : Fin n → ℕ := fun _ => max 1 D
    let F := ProjectionCriticalFamily.spatialEquation q base (fun i => (v i : Polynomial ℤ))
    let N := UniformAffineCoordinates.count d
    let B := UniformAffineCoordinates.bitBudget d (ProjectionCriticalBounds.massExponent b D U)
    ∃ P : Fin n → Polynomial (Polynomial ℤ), ∃ r : Polynomial ℤ,
      r ≠ 0 ∧ r.natDegree ≤ n * (N * E) ∧
      coefficientMass r ≤ ((N * E + 1) * 2 ^ B) ^ n ∧
      (∀ i, P i ≠ 0 ∧ (P i).natDegree ≤ N ∧ (∀ k, ((P i).coeff k).natDegree ≤ N * E) ∧
        ∀ k l, (((P i).coeff k).coeff l).natAbs.size ≤ B) ∧
      ∀ t : ℝ, r.eval₂ (Int.castRingHom ℝ) t ≠ 0 →
        let φ := Polynomial.eval₂RingHom (Int.castRingHom ℝ) t
        (∀ i, (P i).map φ ≠ 0) ∧
        ∀ x : Fin n → ℝ, (∀ j, (F j).eval₂ φ x = 0) →
          (fderiv ℝ (fun y => fun j => (F j).eval₂ φ y) x).IsInvertible →
            ∀ i, ((P i).map φ).eval (x i) = 0 := by
  apply UniformAffineCoordinates.exists_bounded
  · intro j
    exact (ProjectionCriticalBounds.spatial_degree q base v D hD j).trans (le_max_right 1 D)
  · intro j
    exact lt_of_lt_of_le (by decide : 0 < 1) (le_max_left 1 D)
  · exact ProjectionCriticalBounds.spatial_parameter_degree q base v E hdegree
  · exact ProjectionCriticalBounds.spatial_coefficient_mass q base v D U b hD hU hmass

end LeanCanny.Geometry.BoundedCriticalCoordinates
