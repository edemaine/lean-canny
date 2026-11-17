/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SelectionSystem
public import LeanCanny.CountingHierarchy.BoundedTwoTestCriterion

/-! # The controlled selection system expresses the actual bounded root-label selection -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial
open scoped Classical

attribute [local irreducible] addressedCandidateCoordinate candidateCoordinate parametricCoordinatePolynomial

variable {n : ℕ}

theorem eval_indexedCandidateTest (F : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (hn : 0 < n) (word : List Bool) (i : ℕ) (hi : i < n) (x : Fin n → ℝ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) x
      (coordinateTestPolynomial (indexedCandidatePolynomial F D hD hn word i) hn i) =
      (addressedCandidateCoordinate F D hD ⟨i, hi⟩ (choiceIndex (candidateIndexBound n D) word i)).eval₂
        (Int.castRingHom ℝ) (x ⟨i, hi⟩) := by
  rw [eval_coordinateTestPolynomial, indexedCandidatePolynomial]
  simp only [Nat.mod_eq_of_lt hi]

theorem eval_indexedLabelTest (F : MvPolynomial (Fin n) ℤ) (D b : ℕ) (hD : F.totalDegree ≤ D)
    (hn : 0 < n) (word : List Bool) (i : ℕ) (hi : i < n) (x : Fin n → ℝ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) x (selectionInequality F D b hD hn word i) =
      (fingerprintIntegerRootLabel
        (addressedCandidateCoordinate F D hD ⟨i, hi⟩ (choiceIndex (candidateIndexBound n D) word i)) 1
        (candidateDegree n D) (candidateMassExponent n D b)
        (choiceLabel (candidateDegree n D) word i).modulus
        (choiceLabel (candidateDegree n D) word i).parameter
        (choiceLabel (candidateDegree n D) word i).target).eval₂ (Int.castRingHom ℝ) (x ⟨i, hi⟩) := by
  rw [selectionInequality, eval_coordinateTestPolynomial, indexedCandidateLabel, indexedCandidatePolynomial]
  simp only [Nat.mod_eq_of_lt hi]

theorem selection_constraints_iff (F : MvPolynomial (Fin n) ℤ) (D b : ℕ) (hD : F.totalDegree ≤ D)
    (hn : 0 < n) (word : List Bool) (x : Fin n → ℝ) :
    ((∀ i < n + 1, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (selectionEquation F D hD hn word i) = 0) ∧
      ∀ i < n, 0 < MvPolynomial.eval₂ (Int.castRingHom ℝ) x (selectionInequality F D b hD hn word i)) ↔
      candidateSelection F D b hD
        (fun i => choiceIndex (candidateIndexBound n D) word i.val)
        (fun i => choiceLabel (candidateDegree n D) word i.val) x := by
  change _ ↔ MvPolynomial.eval₂ (Int.castRingHom ℝ) x F = 0 ∧ _
  constructor
  · rintro ⟨he, hp⟩
    refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
    · simpa only [selectionEquation, ite_true] using he 0 (by omega)
    · have h := he (i.val + 1) (by have := i.isLt; omega)
      rw [selectionEquation, ite_eq_right (by omega : i.val + 1 ≠ 0)] at h
      simpa only [Nat.add_sub_cancel, eval_indexedCandidateTest F D hD hn word i.val i.isLt x] using h
    · simpa only [eval_indexedLabelTest F D b hD hn word i.val i.isLt x, candidateDegree, candidateMassExponent]
        using hp i.val i.isLt
  · rintro ⟨hF, hc⟩
    constructor
    · intro i hi
      by_cases hz : i = 0
      · subst i
        simpa only [selectionEquation, ite_true] using hF
      · have hi' : i - 1 < n := by omega
        rw [selectionEquation, ite_eq_right hz, eval_indexedCandidateTest F D hD hn word (i - 1) hi' x]
        exact (hc ⟨i - 1, hi'⟩).1
    · intro i hi
      rw [eval_indexedLabelTest F D b hD hn word i hi x]
      simpa only [candidateDegree, candidateMassExponent] using (hc ⟨i, hi⟩).2

end LeanCanny.CountingHierarchy
