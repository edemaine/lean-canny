/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixProductEntry
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# An ordered matrix product as one layered matrix power

Vertices consist of a layer and a coordinate. Edges from layer s to layer s+1
carry entries of factor A s; every other edge is zero. A power entry is zero
unless its exponent equals the layer difference, in which case it is the
corresponding entry of the ordered product interval. No commutativity of
scalar multiplication is needed.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixProduct
open Matrix Finset

variable {R : Type*} [Semiring R] {n : ℕ}

def layered (A : ℕ → Matrix (Fin n) (Fin n) R) (L : ℕ) :
    Matrix (Fin L × Fin n) (Fin L × Fin n) R :=
  fun p q => if p.1.val + 1 = q.1.val then A p.1.val p.2 q.2 else 0

theorem layered_mul_apply (A : ℕ → Matrix (Fin n) (Fin n) R) (L : ℕ)
    (B : Matrix (Fin L × Fin n) (Fin L × Fin n) R)
    (s t : Fin L) (i j : Fin n) :
    (layered A L * B) (s, i) (t, j) =
      if hs : s.val + 1 < L then
        ∑ k, A s.val i k * B (⟨s.val + 1, hs⟩, k) (t, j)
      else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hs : s.val + 1 < L
  · simp only [hs, ↓reduceDIte]
    rw [sum_eq_single (⟨s.val + 1, hs⟩ : Fin L)]
    · simp [layered]
    · intro u _ hu
      have hne : s.val + 1 ≠ u.val := by
        intro h
        exact hu (Fin.ext h.symm)
      simp [layered, hne]
    · simp
  · have hne (u : Fin L) : s.val + 1 ≠ u.val := by have := u.isLt; omega
    simp [hs, layered, hne]

theorem layered_pow_apply (A : ℕ → Matrix (Fin n) (Fin n) R) (L e : ℕ)
    (s t : Fin L) (i j : Fin n) :
    (layered A L ^ e) (s, i) (t, j) =
      if s.val + e = t.val then product A s.val e i j else 0 := by
  induction e generalizing s t i j with
  | zero =>
      by_cases h : s = t
      · subst t; simp [product, Matrix.one_apply]
      · have hval : s.val ≠ t.val := fun he => h (Fin.ext he)
        simp [h, hval]
  | succ e ih =>
      rw [pow_succ', layered_mul_apply]
      by_cases hs : s.val + 1 < L
      · simp only [hs, ↓reduceDIte]
        simp_rw [ih]
        have heq : s.val + 1 + e = t.val ↔ s.val + (e + 1) = t.val := by omega
        simp only [heq]
        by_cases he : s.val + (e + 1) = t.val
        · simp [he, product, Matrix.mul_apply]
        · simp [he]
      · have he : s.val + (e + 1) ≠ t.val := by have := t.isLt; omega
        simp [hs, he]

theorem layered_pow_product (A : ℕ → Matrix (Fin n) (Fin n) R) (s e : ℕ)
    (i j : Fin n) :
    (layered A (s + e + 1) ^ e)
      (⟨s, by omega⟩, i) (⟨s + e, by omega⟩, j) = product A s e i j := by
  rw [layered_pow_apply]
  simp

/-- Row-major flattening of the layer-coordinate pair, using division and
remainder by the factor width in the inverse direction. -/
def layeredFin (A : ℕ → Matrix (Fin n) (Fin n) R) (L : ℕ) :
    Matrix (Fin (L * n)) (Fin (L * n)) R :=
  Matrix.reindexRingEquiv R finProdFinEquiv (layered A L)

theorem layeredFin_apply (A : ℕ → Matrix (Fin n) (Fin n) R) (L : ℕ)
    (p q : Fin (L * n)) :
    layeredFin A L p q =
      if p.divNat.val + 1 = q.divNat.val then A p.divNat.val p.modNat q.modNat else 0 := rfl

theorem layeredFin_pow_apply (A : ℕ → Matrix (Fin n) (Fin n) R) (L e : ℕ)
    (s t : Fin L) (i j : Fin n) :
    (layeredFin A L ^ e) (finProdFinEquiv (s, i)) (finProdFinEquiv (t, j)) =
      if s.val + e = t.val then product A s.val e i j else 0 := by
  unfold layeredFin
  rw [← map_pow]
  simpa only [Matrix.coe_reindexRingEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply] using layered_pow_apply A L e s t i j

theorem layeredFin_pow_product (A : ℕ → Matrix (Fin n) (Fin n) R) (s e : ℕ)
    (i j : Fin n) :
    (layeredFin A (s + e + 1) ^ e)
      (finProdFinEquiv (⟨s, by omega⟩, i))
      (finProdFinEquiv (⟨s + e, by omega⟩, j)) = product A s e i j := by
  rw [layeredFin_pow_apply]
  simp

end LeanCanny.Algebra.MatrixProduct
