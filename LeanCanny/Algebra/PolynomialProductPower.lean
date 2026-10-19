/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.LayeredMatrix
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A polynomial product as one shift-matrix power

A layer carries one scalar coordinate. Its outgoing edge contains the factor
at that layer, so the entry from the first to the last layer in the appropriate
power is the product of all factors. This also covers an empty product: the
zero-th power of the one-vertex matrix has diagonal entry one.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialProduct
open scoped BigOperators

variable {R : Type*} [CommSemiring R]

def scalarVertex (L : ℕ) : (Fin L × Fin 1) ≃ Fin L where
  toFun := Prod.fst
  invFun := fun i => (i, 0)
  left_inv := by intro ⟨i, j⟩; have hj : j = 0 := Subsingleton.elim _ _; simp [hj]
  right_inv := fun _ => rfl

theorem scalarVertex_symm_apply (L : ℕ) (i : Fin L) : (scalarVertex L).symm i = (i, 0) := rfl

def scalar (f : ℕ → R) (k : ℕ) : Matrix (Fin 1) (Fin 1) R := Matrix.of (fun _ _ => f k)

def shift (f : ℕ → R) (L : ℕ) : Matrix (Fin L) (Fin L) R :=
  Matrix.reindexRingEquiv R (scalarVertex L) (MatrixProduct.layered (scalar f) L)

theorem shift_apply (f : ℕ → R) (L : ℕ) (i j : Fin L) :
    shift f L i j = if i.val + 1 = j.val then f i.val else 0 := by
  simp only [shift, Matrix.coe_reindexRingEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    scalarVertex_symm_apply, MatrixProduct.layered, scalar, Matrix.of_apply]
  rfl

theorem scalar_product (f : ℕ → R) (s e : ℕ) :
    MatrixProduct.product (scalar f) s e 0 0 =
      ∏ i ∈ Finset.range e, f (s + i) := by
  induction e generalizing s with
  | zero => simp [MatrixProduct.product]
  | succ e ih =>
    rw [MatrixProduct.product, Matrix.mul_apply]
    simp only [Fin.sum_univ_one]
    rw [ih, Finset.prod_range_succ']
    simp only [scalar, Matrix.of_apply]
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    rw [mul_comm]

theorem shift_pow_apply (f : ℕ → R) (L e : ℕ) (s t : Fin L) :
    (shift f L ^ e) s t = if s.val + e = t.val then ∏ i ∈ Finset.range e, f (s.val + i) else 0 := by
  rw [shift, ← map_pow]
  change (MatrixProduct.layered (scalar f) L ^ e) (s, 0) (t, 0) = _
  rw [MatrixProduct.layered_pow_apply, scalar_product]

theorem shift_pow_product (f : ℕ → R) (N : ℕ) :
    (shift f (N + 1) ^ N) 0 (Fin.last N) = ∏ i ∈ Finset.range N, f i := by
  simp only [shift_pow_apply, Fin.val_zero, Nat.zero_add, Fin.val_last, ↓reduceIte]

end LeanCanny.Algebra.PolynomialProduct
