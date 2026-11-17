/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeTwoTestCriterion
public import LeanCanny.CountingHierarchy.ChoiceTupleCompleteness
public import LeanCanny.CountingHierarchy.ControlledBoundedCandidate

/-! # One fixed-width word suffices for the source-derived two existential tests -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] finiteRelativeSection finiteRelativeCharacteristic
  relativeCharacteristic relativeBivariate specializedRelativeSection firstVariableCoefficient
  degreePiecePolynomial candidateCoordinate parametricCoordinatePolynomial

variable {n m : ℕ}

theorem relative_good_iff_word_two_tests (d : ℕ) (hd : 1 ≤ d) (he : Even (d + 2))
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
      ∃ word : List Bool, word.length = choiceTupleWidth N (candidateIndexBound (m + 1) D)
        (candidateDegree (m + 1) D) (m + 1) ∧
        (∃ c, candidateSelection (W (choiceDegree N word)) D B (hD (choiceDegree N word))
          (fun i => choiceIndex (candidateIndexBound (m + 1) D) word i.val)
          (fun i => choiceLabel (candidateDegree (m + 1) D) word i.val) c) ∧
        ¬∃ c z, candidateSelection (W (choiceDegree N word)) D B (hD (choiceDegree N word))
          (fun i => choiceIndex (candidateIndexBound (m + 1) D) word i.val)
          (fun i => choiceLabel (candidateDegree (m + 1) D) word i.val) c ∧
          MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z (fun i => c i.succ)) P = 0 := by
  dsimp only
  have hmat := relative_good_iff_bounded_two_tests d hd he P hP hFn N b hN hb
  dsimp only at hmat
  rw [hmat]
  constructor
  · rintro ⟨k, j, L, hj, hL, hnonempty, hnocounter⟩
    obtain ⟨word, hlen, hk, hjs, hLs⟩ := exists_choiceTupleWord N
      (candidateIndexBound (m + 1) (2 * (N + 1))) (candidateDegree (m + 1) (2 * (N + 1))) k j L hj hL
    have hjeq : (fun i : Fin (m + 1) => choiceIndex
        (candidateIndexBound (m + 1) (2 * (N + 1))) word i.val) = j := funext hjs
    have hLeq : (fun i : Fin (m + 1) => choiceLabel
        (candidateDegree (m + 1) (2 * (N + 1))) word i.val) = L := funext hLs
    refine ⟨word, hlen, ?_, ?_⟩
    · rw [hk, hjeq, hLeq]
      exact hnonempty
    · rw [hk, hjeq, hLeq]
      exact hnocounter
  · rintro ⟨word, _, hnonempty, hnocounter⟩
    exact ⟨choiceDegree N word, _, _, (fun i => choiceIndex_le _ _ _),
      (fun i => choiceLabel_bounded _ _ _), hnonempty, hnocounter⟩

end LeanCanny.CountingHierarchy
