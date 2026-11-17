/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CoordinateCandidateBounds
public import LeanCanny.CountingHierarchy.CoordinateCriticalLimits

/-! # Bounds for every addressed coefficient used by candidate-coordinate sampling -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial LeanCanny.Algebra

variable {n : ℕ}

noncomputable def addressedCandidateCoordinate (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) (j : ℕ) : Polynomial ℤ :=
  (Bivariate.swap (parametricCoordinatePolynomial (2 * (D + 1)) (q ^ 2)
    (totalDegree_pow q 2 |>.trans (by nlinarith)) i)).coeff j

noncomputable def candidateCoordinateIndex (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) : ℕ :=
  (Bivariate.swap (parametricCoordinatePolynomial (2 * (D + 1)) (q ^ 2)
    (totalDegree_pow q 2 |>.trans (by nlinarith)) i)).natDegree

theorem addressedCandidateCoordinate_at_index (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) :
    addressedCandidateCoordinate q D hD i (candidateCoordinateIndex q D hD i) = candidateCoordinate q D hD i := rfl

theorem candidateCoordinateIndex_le (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) :
    candidateCoordinateIndex q D hD i ≤ coordinateParameterDegreeBound n (2 * (D + 1)) :=
  coordinateCandidate_index_bound _ (by omega) _ _ i

theorem addressedCandidateCoordinate_degree_le (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (i : Fin n) (j : ℕ) :
    (addressedCandidateCoordinate q D hD i j).natDegree ≤ (2 * (D + 1) + 1) ^ n :=
  coordinateCandidate_degree_le _ _ _ i j

theorem addressedCandidateCoordinate_mass_le (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) (i : Fin n) (j : ℕ) :
    coefficientMass (addressedCandidateCoordinate q D hD i j) ≤
      2 ^ coordinateCharacteristicMassExponent n (2 * (D + 1)) (2 * b) := by
  apply coordinateCandidate_mass_le _ _ (by omega) _ _ _ i j
  exact (MvMass.pow_le q 2).trans (by
    simpa only [← pow_mul, Nat.mul_comm b 2] using Nat.pow_le_pow_left hb 2)

end LeanCanny.CountingHierarchy
