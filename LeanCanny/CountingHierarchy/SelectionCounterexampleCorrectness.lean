/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SelectionCounterexampleSystem
public import LeanCanny.CountingHierarchy.SelectionSystemCorrectness

/-! # The second existential system selects exactly the counterexamples -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped Classical

variable {n u : ℕ}

theorem selection_extra_constraints_iff (F : MvPolynomial (Fin n) ℤ)
    (R : MvPolynomial (Fin (n + u)) ℤ) (D b : ℕ) (hD : F.totalDegree ≤ D) (hn : 0 < n)
    (word : List Bool) (c : Fin n → ℝ) (z : Fin u → ℝ) :
    ((∀ i < n + 2, MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases c z)
      (selectionExtraEquation F R D hD hn word i) = 0) ∧
      ∀ i < n, 0 < MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases c z)
        (selectionExtraInequality F D b hD hn word i)) ↔
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases c z) R = 0 ∧
        candidateSelection F D b hD
          (fun i => choiceIndex (candidateIndexBound n D) word i.val)
          (fun i => choiceLabel (candidateDegree n D) word i.val) c := by
  have hrename (P : MvPolynomial (Fin n) ℤ) : MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases c z)
      (MvPolynomial.rename (Fin.castAdd u) P) = MvPolynomial.eval₂ (Int.castRingHom ℝ) c P := by
    rw [MvPolynomial.eval₂_rename]
    simp only [Function.comp_def, Fin.addCases_left]
  rw [← selection_constraints_iff F D b hD hn word c]
  constructor
  · rintro ⟨he, hp⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [selectionExtraEquation, ite_true] using he 0 (by omega)
    · intro i hi
      have h := he (i + 1) (by omega)
      simpa only [selectionExtraEquation, ite_eq_right (by omega : i + 1 ≠ 0), Nat.add_sub_cancel,
        hrename] using h
    · intro i hi
      simpa only [selectionExtraInequality, hrename] using hp i hi
  · rintro ⟨hR, he, hp⟩
    constructor
    · intro i hi
      by_cases hz : i = 0
      · subst i
        simpa only [selectionExtraEquation, ite_true] using hR
      · rw [selectionExtraEquation, ite_eq_right hz, hrename]
        exact he (i - 1) (by omega)
    · intro i hi
      simpa only [selectionExtraInequality, hrename] using hp i hi

theorem exists_selectionSystem_zero_iff (F : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : F.totalDegree ≤ D) (hn : 0 < n) (word : List Bool) :
    (∃ y : Fin (n + n) → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) y
      (indexedEquationPositivityPolynomial (selectionEquation F D hD hn word)
        (selectionInequality F D b hD hn word) (n + 1) n) = 0) ↔
      ∃ c, candidateSelection F D b hD
        (fun i => choiceIndex (candidateIndexBound n D) word i.val)
        (fun i => choiceLabel (candidateDegree n D) word i.val) c := by
  rw [exists_indexedEquationPositivityPolynomial_zero_iff]
  exact exists_congr (selection_constraints_iff F D b hD hn word)

theorem exists_selectionCounterexampleSystem_zero_iff (F : MvPolynomial (Fin n) ℤ)
    (R : MvPolynomial (Fin (n + u)) ℤ) (D b : ℕ) (hD : F.totalDegree ≤ D)
    (hn : 0 < n) (word : List Bool) :
    (∃ y : Fin ((n + u) + n) → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) y
      (indexedEquationPositivityPolynomial (selectionExtraEquation F R D hD hn word)
        (selectionExtraInequality F D b hD hn word) (n + 2) n) = 0) ↔
      ∃ c : Fin n → ℝ, ∃ z : Fin u → ℝ, candidateSelection F D b hD
        (fun i => choiceIndex (candidateIndexBound n D) word i.val)
        (fun i => choiceLabel (candidateDegree n D) word i.val) c ∧
        MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases c z) R = 0 := by
  rw [exists_indexedEquationPositivityPolynomial_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    let c : Fin n → ℝ := fun i => y (Fin.castAdd u i)
    let z : Fin u → ℝ := fun i => y (Fin.natAdd n i)
    have hjoin : Fin.addCases c z = y := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.addCases_left]
      · rw [Fin.addCases_right]
    rw [← hjoin, selection_extra_constraints_iff] at hy
    exact ⟨c, z, hy.2, hy.1⟩
  · rintro ⟨c, z, hc, hR⟩
    exact ⟨Fin.addCases c z, (selection_extra_constraints_iff F R D b hD hn word c z).mpr ⟨hR, hc⟩⟩

end LeanCanny.CountingHierarchy
