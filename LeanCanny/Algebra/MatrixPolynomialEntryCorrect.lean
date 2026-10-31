/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPolynomialEntrySpace
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Data.Matrix.Basic

/-! # Native entries of actual polynomial evaluations at matrices

A binary coefficient allowance above the polynomial degree identifies the
streamed coefficient sum with polynomial evaluation by scalar matrices.
The polynomial is semantic data; only its coefficient reader is used.
-/

@[expose] public section
namespace LeanCanny.Algebra.MatrixPolynomialEntryBits
open LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem polynomial_entry {R : Type*} [CommRing R] {n : ℕ} (p : Polynomial R)
    (A : Matrix (Fin n) (Fin n) R) (count : ℕ) (hp : p.natDegree < count) (i j : Fin n) :
    (p.eval₂ (Matrix.scalar (Fin n)) A) i j =
      ∑ k ∈ Finset.range count, p.coeff k * (A ^ k) i j := by
  rw [Polynomial.eval₂_eq_sum_range' _ hp]
  simp only [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem map_polynomial_entry {R : Type*} [CommRing R] {n : ℕ} (φ : ℤ →+* R) (p : Polynomial ℤ)
    (A : Matrix (Fin n) (Fin n) ℤ) (count : ℕ) (hp : p.natDegree < count) (i j : Fin n) :
    φ ((p.eval₂ (Matrix.scalar (Fin n)) A) i j) =
      ((p.map φ).eval₂ (Matrix.scalar (Fin n)) (A.map φ)) i j := by
  rw [polynomial_entry p A count hp, polynomial_entry (p.map φ) (A.map φ) count
    ((Polynomial.natDegree_map_le).trans_lt hp), map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_mul, Polynomial.coeff_map, ← Matrix.map_pow, Matrix.map_apply]

theorem polynomial_evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) (C : SpaceFunction a.coefficient)
    (p : (c : List Bool) → Polynomial (ZMod (F.modulus c))) (hp : ∀ c, (p c).natDegree < F.count c)
    (hc : ∀ c k, (p c).coeff k = F.coefficient c k) :
    SpaceFunction (fun c => residueBits (((p c).eval₂ (Matrix.scalar (Fin (F.dimension c))) (F.matrix c)) (F.row c) (F.col c))) := by
  refine (evaluator F a E C).congr (funext fun c => ?_)
  rw [polynomial_entry _ _ _ (hp c)]
  simp only [Family.value, hc]

end LeanCanny.Algebra.MatrixPolynomialEntryBits
