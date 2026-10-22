/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalCoordinatePath
public import LeanCanny.Algebra.UnivariateRationalSubstitutionMatrix
public import LeanCanny.Algebra.LayeredMatrix

/-! # A whole rational-coordinate path as one layered matrix power

The same substitution matrices act on numerator and denominator coefficients.
Their initial vectors are X and one, so rows one and zero of the product
recover the two complete output polynomials. The finite coefficient width
must exceed every clearing exponent along the path.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalCoordinatePath
open Polynomial UnivariateRational

noncomputable def matrices (N D : ℕ) (inner : ℕ → Coordinate) (s : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  clearingMatrix N (D ^ s) (inner s).numerator (inner s).denominator

theorem vectors_product (N D : ℕ) (inner : ℕ → Coordinate) (k : ℕ)
    (he : ∀ s < k, D ^ s < N) :
    Matrix.vecMul (fun i : Fin N => (X : ℤ[X]).coeff i.val) (MatrixProduct.product (matrices N D inner) 0 k) =
      (fun j : Fin N => (path D inner k).numerator.coeff j.val) ∧
    Matrix.vecMul (fun i : Fin N => (1 : ℤ[X]).coeff i.val) (MatrixProduct.product (matrices N D inner) 0 k) =
      (fun j : Fin N => (path D inner k).denominator.coeff j.val) := by
  induction k with
  | zero => simp only [MatrixProduct.product, Matrix.vecMul_one, path, BalancedPrimitiveTree.identityCoordinate, and_self]
  | succ k ih =>
    have H := ih (fun s hs => he s (by omega))
    have hp : MatrixProduct.product (matrices N D inner) 0 (k + 1) =
        MatrixProduct.product (matrices N D inner) 0 k * matrices N D inner k := by
      rw [MatrixProduct.product_add, MatrixProduct.product]
      simp only [MatrixProduct.product, Nat.zero_add, Matrix.mul_one]
    constructor
    · rw [hp, ← Matrix.vecMul_vecMul, H.1]
      funext j
      exact vecMul_clearingMatrix N (D ^ k) (path D inner k).numerator (inner k).numerator (inner k).denominator (he k (by omega)) j
    · rw [hp, ← Matrix.vecMul_vecMul, H.2]
      funext j
      exact vecMul_clearingMatrix N (D ^ k) (path D inner k).denominator (inner k).numerator (inner k).denominator (he k (by omega)) j

private theorem basis_vecMul (N : ℕ) (t : Fin N) (A : Matrix (Fin N) (Fin N) ℤ) :
    Matrix.vecMul (fun i => if i = t then 1 else 0) A = A t := by
  funext j
  simp [Matrix.vecMul, dotProduct, ite_mul]

theorem product_entries (N D : ℕ) (inner : ℕ → Coordinate) (k : ℕ)
    (hN : 1 < N) (he : ∀ s < k, D ^ s < N) (j : Fin N) :
    MatrixProduct.product (matrices N D inner) 0 k ⟨1, hN⟩ j = (path D inner k).numerator.coeff j.val ∧
    MatrixProduct.product (matrices N D inner) 0 k ⟨0, by omega⟩ j = (path D inner k).denominator.coeff j.val := by
  have hx : (fun i : Fin N => (X : ℤ[X]).coeff i.val) = (fun i => if i = (⟨1, hN⟩ : Fin N) then 1 else 0) := by
    funext i
    simp only [Polynomial.coeff_X, Fin.ext_iff, eq_comm]
  have h1 : (fun i : Fin N => (1 : ℤ[X]).coeff i.val) = (fun i => if i = (⟨0, by omega⟩ : Fin N) then 1 else 0) := by
    funext i
    simp only [Polynomial.coeff_one, Fin.ext_iff]
  have H := vectors_product N D inner k he
  rw [hx, basis_vecMul] at H
  rw [h1, basis_vecMul] at H
  exact ⟨congrFun H.1 j, congrFun H.2 j⟩

theorem layered_entries (N D : ℕ) (inner : ℕ → Coordinate) (k : ℕ)
    (hN : 1 < N) (he : ∀ s < k, D ^ s < N) (j : Fin N) :
    (MatrixProduct.layeredFin (matrices N D inner) (k + 1) ^ k)
      (finProdFinEquiv (⟨0, by omega⟩, ⟨1, hN⟩)) (finProdFinEquiv (⟨k, by omega⟩, j)) =
        (path D inner k).numerator.coeff j.val ∧
    (MatrixProduct.layeredFin (matrices N D inner) (k + 1) ^ k)
      (finProdFinEquiv (⟨0, by omega⟩, ⟨0, by omega⟩)) (finProdFinEquiv (⟨k, by omega⟩, j)) =
        (path D inner k).denominator.coeff j.val := by
  have H := product_entries N D inner k hN he j
  rw [MatrixProduct.layeredFin_pow_apply, MatrixProduct.layeredFin_pow_apply]
  simpa only [Nat.zero_add, ite_true] using H

end LeanCanny.Algebra.RationalCoordinatePath

namespace LeanCanny.Algebra.MatrixProduct

theorem product_map {R S : Type*} [Semiring R] [Semiring S] {N : ℕ}
    (f : R →+* S) (A : ℕ → Matrix (Fin N) (Fin N) R) (s k : ℕ) :
    product (fun j => (A j).map f) s k = (product A s k).map f := by
  induction k generalizing s with
  | zero =>
    ext i j
    by_cases h : i = j <;> simp [product, Matrix.map_apply, Matrix.one_apply, h]
  | succ k ih =>
    simp only [product, ih]
    exact (map_mul f.mapMatrix _ _).symm

end LeanCanny.Algebra.MatrixProduct
