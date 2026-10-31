/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PurePowerRelativeAnnihilator

/-! # Independence of the unused pure-power fallback coordinate

A nonnormal monomial has a violating coordinate, so its selected coordinate
is independent of the fallback. Normal columns never use the selection.
Consequently the actual reduction, action, and relative polynomial are
unchanged when the fallback differs from the requested root coordinate.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerReductionMatrix
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n B : ℕ} {R : Type*} [CommRing R]

theorem selected_fallback (a b : Fin n) (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (h : ¬ Normal d e) :
    selected a d e = selected b d e := by
  have H : (candidates d e).Nonempty :=
    ⟨selected a d e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, selected_divides a d e h⟩⟩
  simp only [selected, dite_eq_left H]

theorem matrix_fallback (a b : Fin n) (d : Fin n → ℕ) (low : Fin n → MvPolynomial (Fin n) R)
    (c : R) (bound : ℕ) : matrix (B := B) a d low c bound = matrix b d low c bound := by
  ext i j
  dsimp only [matrix]
  by_cases h : Normal d (FixedWidthPolynomial.vector n B j)
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h, selected_fallback a b d _ h]

end LeanCanny.Algebra.PurePowerReductionMatrix

namespace LeanCanny.Algebra.PurePowerRelativeAnnihilator
open PurePowerReductionMatrix
set_option backward.isDefEq.respectTransparency false
variable {n B : ℕ} {R : Type*} [CommRing R]

theorem action_fallback (a b : Fin n) (d : Fin n → ℕ) (low : Fin n → MvPolynomial (Fin n) R)
    (c : R) (bound : ℕ) (hgrid : gridBound d + 1 ≤ bound) (hbound : bound < 2 ^ B) (r : Fin n) :
    actionMatrix a d low c bound hgrid hbound r = actionMatrix b d low c bound hgrid hbound r := by
  unfold actionMatrix
  rw [matrix_fallback a b]

theorem polynomial_fallback (a b : Fin n) (d : Fin n → ℕ) (low : Fin n → MvPolynomial (Fin n) R)
    (c : R) (bound : ℕ) (hgrid : gridBound d + 1 ≤ bound) (hbound : bound < 2 ^ B) (r : Fin n) :
    polynomial a d low c bound hgrid hbound r = polynomial b d low c bound hgrid hbound r := by
  unfold polynomial
  rw [action_fallback a b]

end LeanCanny.Algebra.PurePowerRelativeAnnihilator
