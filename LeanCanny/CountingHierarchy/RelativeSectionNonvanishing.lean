/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativePowerSection

/-! # The actual fixed-power section is nonzero on every parameter fiber -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial

variable {n m : ℕ}

noncomputable def specializedRelativeSection (d : ℕ) (P : MvPolynomial (Fin (n + m)) ℤ)
    (hP : P.totalDegree ≤ d + 1) (x : Fin m → ℝ) : Polynomial ℝ :=
  (MvPolynomial.finSuccEquiv ℤ m (finiteRelativeSection d P hP)).map
    (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) x)

theorem specializedRelativeSection_eq (d : ℕ) (P : MvPolynomial (Fin (n + m)) ℤ)
    (hP : P.totalDegree ≤ d + 1) (x : Fin m → ℝ) :
    specializedRelativeSection d P hP x =
      monicPowerSubstitution ((d + 1) ^ n)
        (relativeBivariate d (MvPolynomial.rename finSumFinEquiv.symm P)
          ((MvPolynomial.totalDegree_rename_le _ _).trans hP) x) := by
  apply Polynomial.funext
  intro v
  rw [specializedRelativeSection, Polynomial.eval_map, eval_finSuccEquiv, eval_finiteRelativeSection]
  induction relativeBivariate d (MvPolynomial.rename finSumFinEquiv.symm P)
      ((MvPolynomial.totalDegree_rename_le _ _).trans hP) x using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval₂_add, monicPowerSubstitution, Polynomial.eval₂_add,
      Polynomial.eval_add, hp, hq]
  | monomial k a =>
    rw [monicPowerSubstitution, Polynomial.eval₂_monomial, Polynomial.eval₂_monomial,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    congr 1
    exact (Polynomial.expand_eval ((d + 1) ^ n + 1) a v).symm

theorem specializedRelativeSection_ne_zero (d : ℕ) (P : MvPolynomial (Fin (n + m)) ℤ)
    (hP : P.totalDegree ≤ d + 1) (x : Fin m → ℝ) : specializedRelativeSection d P hP x ≠ 0 := by
  rw [specializedRelativeSection_eq]
  exact relativePowerSection_ne_zero d _ _ x

end LeanCanny.CountingHierarchy
