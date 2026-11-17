/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled
public import Mathlib.Analysis.Real.Sqrt

/-! # Equations and strict inequalities as one integer polynomial equation -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped BigOperators Classical

variable {n e k : ℕ}

theorem positive_iff_exists_square_inverse (a : ℝ) : 0 < a ↔ ∃ s : ℝ, a * s ^ 2 = 1 := by
  constructor
  · intro ha
    exact ⟨Real.sqrt (a⁻¹), by rw [Real.sq_sqrt (inv_nonneg.mpr ha.le), mul_inv_cancel₀ ha.ne']⟩
  · rintro ⟨s, hs⟩
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (sq_nonneg s)
    linarith

noncomputable def equationPositivityPolynomial
    (P : Fin e → MvPolynomial (Fin n) ℤ) (Q : Fin k → MvPolynomial (Fin n) ℤ) :
    MvPolynomial (Fin (n + k)) ℤ :=
  (∑ i : Fin e, MvPolynomial.rename (Fin.castAdd k) (P i) ^ 2) +
    ∑ i : Fin k, (MvPolynomial.rename (Fin.castAdd k) (Q i) * MvPolynomial.X (Fin.natAdd n i) ^ 2 - 1) ^ 2

attribute [local irreducible] equationPositivityPolynomial

theorem equationPositivityPolynomial_zero_iff
    (P : Fin e → MvPolynomial (Fin n) ℤ) (Q : Fin k → MvPolynomial (Fin n) ℤ)
    (x : Fin n → ℝ) (s : Fin k → ℝ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases x s) (equationPositivityPolynomial P Q) = 0 ↔
      (∀ i, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (P i) = 0) ∧
        ∀ i, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (Q i) * s i ^ 2 = 1 := by
  have hrename (p : MvPolynomial (Fin n) ℤ) :
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases x s) (MvPolynomial.rename (Fin.castAdd k) p) =
        MvPolynomial.eval₂ (Int.castRingHom ℝ) x p := by
    rw [MvPolynomial.eval₂_rename]
    simp only [Function.comp_def, Fin.addCases_left]
  simp only [equationPositivityPolynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_one, hrename, Fin.addCases_right]
  rw [add_eq_zero_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _), Finset.mem_univ, forall_true_left,
    sq_eq_zero_iff, sub_eq_zero]

theorem exists_equationPositivityPolynomial_zero_iff
    (P : Fin e → MvPolynomial (Fin n) ℤ) (Q : Fin k → MvPolynomial (Fin n) ℤ) :
    (∃ z : Fin (n + k) → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) z (equationPositivityPolynomial P Q) = 0) ↔
      ∃ x : Fin n → ℝ, (∀ i, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (P i) = 0) ∧
        ∀ i, 0 < MvPolynomial.eval₂ (Int.castRingHom ℝ) x (Q i) := by
  constructor
  · rintro ⟨z, hz⟩
    let x : Fin n → ℝ := fun i => z (i.castAdd k)
    let s : Fin k → ℝ := fun i => z (i.natAdd n)
    have hz' : Fin.addCases x s = z := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.addCases_left]
      · rw [Fin.addCases_right]
    rw [← hz', equationPositivityPolynomial_zero_iff] at hz
    exact ⟨x, hz.1, fun i => (positive_iff_exists_square_inverse _).mpr ⟨s i, hz.2 i⟩⟩
  · rintro ⟨x, hP, hQ⟩
    choose s hs using fun i => (positive_iff_exists_square_inverse _).mp (hQ i)
    exact ⟨Fin.addCases x s, (equationPositivityPolynomial_zero_iff P Q x s).mpr ⟨hP, hs⟩⟩

end LeanCanny.CountingHierarchy
