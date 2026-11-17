/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FirstVariableCoefficients
public import LeanCanny.CountingHierarchy.DegreePieceClosedLift

/-! # Integer polynomials for the closed lift of a degree piece -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped BigOperators Classical

variable {n : ℕ}

/-- Coordinate zero is the inverse of the selected nonzero coefficient. -/
noncomputable def liftedFirstCoefficient (P : MvPolynomial (Fin (n + 1)) ℤ) (k : ℕ) :
    MvPolynomial (Fin (n + 1)) ℤ := MvPolynomial.rename Fin.succ (firstVariableCoefficient P k)

noncomputable def degreePiecePolynomial (P : MvPolynomial (Fin (n + 1)) ℤ) (N d : ℕ) :
    MvPolynomial (Fin (n + 1)) ℤ :=
  (liftedFirstCoefficient P d * MvPolynomial.X 0 - 1) ^ 2 +
    ∑ j ∈ Finset.range (N + 1), if d < j then liftedFirstCoefficient P j ^ 2 else 0

theorem eval_liftedFirstCoefficient (P : MvPolynomial (Fin (n + 1)) ℤ) (k : ℕ)
    (t : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.cons t x) (liftedFirstCoefficient P k) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x (firstVariableCoefficient P k) := by
  rw [liftedFirstCoefficient, MvPolynomial.eval₂_rename]
  rfl

theorem eval_degreePiecePolynomial (P : MvPolynomial (Fin (n + 1)) ℤ) (N : ℕ)
    (d : Fin (N + 1)) (t : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.cons t x) (degreePiecePolynomial P N d.val) =
      degreePieceLiftValue (fun j : Fin (N + 1) => fun x : Fin n → ℝ =>
        MvPolynomial.eval₂ (Int.castRingHom ℝ) x (firstVariableCoefficient P j.val)) d (x, t) := by
  simp only [degreePiecePolynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_one, MvPolynomial.eval₂_X,
    Fin.cons_zero, eval_liftedFirstCoefficient, MvPolynomial.eval₂_sum, degreePieceLiftValue]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [MvPolynomial.eval₂_pow, MvPolynomial.eval₂_zero,
    eval_liftedFirstCoefficient]

end LeanCanny.CountingHierarchy
