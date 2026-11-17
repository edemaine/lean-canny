/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeCandidateCoverage
public import LeanCanny.CountingHierarchy.BoundedTwoTestCriterion
public import LeanCanny.CountingHierarchy.DegreePiecePolynomialBounds

/-! # The two existential tests for a source-derived existential-universal sentence -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] finiteRelativeSection finiteRelativeCharacteristic
  relativeCharacteristic relativeBivariate specializedRelativeSection firstVariableCoefficient
  degreePiecePolynomial candidateCoordinate parametricCoordinatePolynomial

variable {n m : ℕ}

theorem relative_good_iff_bounded_two_tests (d : ℕ) (hd : 1 ≤ d) (he : Even (d + 2))
    (P : MvPolynomial (Fin (n + m)) ℤ) (hP : P.totalDegree ≤ d + 1)
    (hFn : ∀ x z, 0 ≤ MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) P)
    (N b : ℕ) (hN : (finiteRelativeSection d P hP).totalDegree ≤ N)
    (hb : MvMass.mass (finiteRelativeSection d P hP) ≤ 2 ^ b) :
    let E := finiteRelativeSection d P hP
    let W := fun k : Fin (N + 1) => degreePiecePolynomial E N k.val
    let D := 2 * (N + 1)
    let B := degreePieceMassExponent N b
    let hD : ∀ k, (W k).totalDegree ≤ D := fun k =>
      (degreePiecePolynomial_degree_le E N k.val).trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hN 1))
    (∃ x : Fin m → ℝ, ∀ z : Fin n → ℝ,
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) P ≠ 0) ↔
      ∃ k : Fin (N + 1), ∃ j : Fin (m + 1) → ℕ, ∃ L : Fin (m + 1) → FingerprintLabelData,
        (∀ i, j i ≤ coordinateParameterDegreeBound (m + 1) (2 * (D + 1))) ∧
        (∀ i, (L i).Bounded ((2 * (D + 1) + 1) ^ (m + 1))) ∧
        (∃ c, candidateSelection (W k) D B (hD k) j L c) ∧
        ¬∃ c z, candidateSelection (W k) D B (hD k) j L c ∧
          MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z (fun i => c i.succ)) P = 0 := by
  dsimp only
  let E := finiteRelativeSection d P hP
  have hD (k : Fin (N + 1)) : (degreePiecePolynomial E N k.val).totalDegree ≤ 2 * (N + 1) :=
    (degreePiecePolynomial_degree_le E N k.val).trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hN 1))
  apply good_parameter_iff_bounded_two_tests
    (fun k : Fin (N + 1) => degreePiecePolynomial E N k.val) (2 * (N + 1)) (degreePieceMassExponent N b)
    hD (fun k => degreePiecePolynomial_mass_le E N k.val b hb)
    (fun c : Fin (m + 1) → ℝ => fun i : Fin m => c i.succ)
    (fun (x : Fin m → ℝ) (z : Fin n → ℝ) => MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) P = 0)
  rintro ⟨x, hx⟩
  obtain ⟨k, c, hc, hroots⟩ := relative_candidate_covers_good_fiber d hd he P hP hFn N hN
    (2 * (N + 1)) hD ⟨x, fun h => by obtain ⟨z, hz⟩ := h; exact hx z hz⟩
  exact ⟨k, c, fun z hz => hc ⟨z, hz⟩, hroots⟩

end LeanCanny.CountingHierarchy
