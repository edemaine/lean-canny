/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalTower

/-! # Retaining affine levels when ancestry grows

Appending critical blocks changes the number of ancestors, but a retained
height or midpoint must continue to refer to its original blocks.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineCriticalTower.Level
open MvPolynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n k m : ℕ} {R : Type*}

def extend (h : k ≤ m) : Level n k R → Level n m R
  | .constant c => .constant c
  | .height j a => .height (j.castLE h) a
  | .midpoint l r a => .midpoint (l.castLE h) (r.castLE h) a

theorem extend_refl (b : Level n k R) : extend (le_refl k) b = b := by
  cases b <;> rfl

theorem extend_trans (h : k ≤ m) {t : ℕ} (g : m ≤ t) (b : Level n k R) :
    extend g (extend h b) = extend (h.trans g) b := by
  cases b <;> rfl

theorem bounded_extend (h : k ≤ m) (b : Level n k ℤ) (U B : ℕ) :
    (extend h b).Bounded U B ↔ b.Bounded U B := by
  cases b <;> rfl

theorem eval_extend [CommRing R] {K : Type*} [CommRing K]
    (φ : R →+* K) (h : k ≤ m) (b : Level n k R)
    (x : Ancestors n k → K) (y : Ancestors n m → K)
    (hy : ∀ (j : Fin k) (i : Fin n), y (oldAmbient m (j.castLE h) i) = x (oldAmbient k j i)) :
    (extend h b).polynomial.eval₂ φ y = b.polynomial.eval₂ φ x := by
  cases b with
  | constant c => simp [extend, polynomial]
  | height j a =>
    simp only [extend, eval_height, hy]
  | midpoint l r a =>
    simp only [extend, eval_midpoint, hy]

theorem eval_extend_prefix [CommRing R] {K : Type*} [CommRing K]
    (φ : R →+* K) (h : k ≤ m) (b : Level n k R)
    (y : Fin (m * width n) → K) :
    (extend h b).polynomial.eval₂ φ (y ∘ TriangularPolynomialIndexing.enumerate (width n) m) =
      b.polynomial.eval₂ φ
        (y ∘ TriangularPolynomialRows.prefixIndex (width n) k m h ∘
          TriangularPolynomialIndexing.enumerate (width n) k) := by
  apply eval_extend
  intro j i
  simp only [Function.comp_apply]
  congr 1
  apply Fin.ext
  rw [oldAmbient_index]
  change j.val * width n + i.val =
    (TriangularPolynomialIndexing.enumerate (width n) k (oldAmbient k j i)).val
  exact (oldAmbient_index k j i).symm

end LeanCanny.Algebra.FlatAffineCriticalTower.Level
