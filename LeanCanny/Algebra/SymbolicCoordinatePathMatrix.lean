/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicCoordinateCompositionWith
public import LeanCanny.Algebra.UnivariateRationalSubstitutionMatrix
public import LeanCanny.Algebra.LayeredMatrix

/-! # Whole symbolic coordinate paths as polynomial matrix products -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicClearingMatrix
open Polynomial
open scoped Classical
variable {R : Type*} [CommRing R]
noncomputable def clearingMatrix (N e : ℕ) (n d : R[X]) : Matrix (Fin N) (Fin N) R :=
  fun i j => if i.val ≤ e then (n ^ i.val * d ^ (e - i.val)).coeff j.val else 0

theorem vecMul_clearingMatrix (N e : ℕ) (p n d : R[X]) (he : e < N) (j : Fin N) :
    Matrix.vecMul (fun k : Fin N => p.coeff k.val) (clearingMatrix N e n d) j = (UnivariateRational.clear e p n d).coeff j.val := by
  change (∑ k : Fin N, p.coeff k.val * (if k.val ≤ e then (n ^ k.val * d ^ (e - k.val)).coeff j.val else 0)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun k => p.coeff k * (if k ≤ e then (n ^ k * d ^ (e - k)).coeff j.val else 0)) N]
  simp only [UnivariateRational.clear, finsetSum_coeff, mul_assoc, coeff_C_mul]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hs : (Finset.range N).filter (fun k => k ≤ e) = Finset.range (e + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hs]

end LeanCanny.Algebra.SymbolicClearingMatrix

namespace LeanCanny.Algebra.SymbolicCoordinatePath
open Polynomial SymbolicBalancedCoordinate
open SymbolicClearingMatrix
open scoped Classical

noncomputable def path (e : ℕ → ℕ) (inner : ℕ → Coordinate) : ℕ → Coordinate
  | 0 => SymbolicBalancedCoordinate.identity
  | k + 1 => Coordinate.compWith (e k) (path e inner k) (inner k)

noncomputable def matrices (N : ℕ) (e : ℕ → ℕ) (inner : ℕ → Coordinate) (s : ℕ) : Matrix (Fin N) (Fin N) (Polynomial ℤ) :=
  clearingMatrix N (e s) (inner s).numerator (inner s).denominator

theorem vectors_product (N : ℕ) (e : ℕ → ℕ) (inner : ℕ → Coordinate) (k : ℕ)
    (he : ∀ s < k, e s < N) :
    Matrix.vecMul (fun i : Fin N => (X : Polynomial (Polynomial ℤ)).coeff i.val) (MatrixProduct.product (matrices N e inner) 0 k) =
      (fun j : Fin N => (path e inner k).numerator.coeff j.val) ∧
    Matrix.vecMul (fun i : Fin N => (1 : Polynomial (Polynomial ℤ)).coeff i.val) (MatrixProduct.product (matrices N e inner) 0 k) =
      (fun j : Fin N => (path e inner k).denominator.coeff j.val) := by
  induction k with
  | zero => simp only [MatrixProduct.product, Matrix.vecMul_one, path, SymbolicBalancedCoordinate.identity, and_self]
  | succ k ih =>
    have H := ih (fun s hs => he s (by omega))
    have hp : MatrixProduct.product (matrices N e inner) 0 (k + 1) =
        MatrixProduct.product (matrices N e inner) 0 k * matrices N e inner k := by
      rw [MatrixProduct.product_add, MatrixProduct.product]
      simp only [MatrixProduct.product, Nat.zero_add, Matrix.mul_one]
    constructor
    · rw [hp, ← Matrix.vecMul_vecMul, H.1]
      funext j
      exact vecMul_clearingMatrix N (e k) (path e inner k).numerator (inner k).numerator (inner k).denominator (he k (by omega)) j
    · rw [hp, ← Matrix.vecMul_vecMul, H.2]
      funext j
      exact vecMul_clearingMatrix N (e k) (path e inner k).denominator (inner k).numerator (inner k).denominator (he k (by omega)) j

private theorem basis_vecMul (N : ℕ) (t : Fin N) (A : Matrix (Fin N) (Fin N) (Polynomial ℤ)) :
    Matrix.vecMul (fun i => if i = t then 1 else 0) A = A t := by
  funext j
  simp [Matrix.vecMul, dotProduct, ite_mul]

theorem product_entries (N : ℕ) (e : ℕ → ℕ) (inner : ℕ → Coordinate) (k : ℕ)
    (hN : 1 < N) (he : ∀ s < k, e s < N) (j : Fin N) :
    MatrixProduct.product (matrices N e inner) 0 k ⟨1, hN⟩ j = (path e inner k).numerator.coeff j.val ∧
    MatrixProduct.product (matrices N e inner) 0 k ⟨0, by omega⟩ j = (path e inner k).denominator.coeff j.val := by
  have hx : (fun i : Fin N => (X : Polynomial (Polynomial ℤ)).coeff i.val) = (fun i => if i = (⟨1, hN⟩ : Fin N) then 1 else 0) := by
    funext i
    simp only [Polynomial.coeff_X, Fin.ext_iff, eq_comm]
  have h1 : (fun i : Fin N => (1 : Polynomial (Polynomial ℤ)).coeff i.val) = (fun i => if i = (⟨0, by omega⟩ : Fin N) then 1 else 0) := by
    funext i
    simp only [Polynomial.coeff_one, Fin.ext_iff]
  have H := vectors_product N e inner k he
  rw [hx, basis_vecMul] at H
  rw [h1, basis_vecMul] at H
  exact ⟨congrFun H.1 j, congrFun H.2 j⟩

theorem layered_entries (N : ℕ) (e : ℕ → ℕ) (inner : ℕ → Coordinate) (k : ℕ)
    (hN : 1 < N) (he : ∀ s < k, e s < N) (j : Fin N) :
    (MatrixProduct.layeredFin (matrices N e inner) (k + 1) ^ k)
      (finProdFinEquiv (⟨0, by omega⟩, ⟨1, hN⟩)) (finProdFinEquiv (⟨k, by omega⟩, j)) =
        (path e inner k).numerator.coeff j.val ∧
    (MatrixProduct.layeredFin (matrices N e inner) (k + 1) ^ k)
      (finProdFinEquiv (⟨0, by omega⟩, ⟨0, by omega⟩)) (finProdFinEquiv (⟨k, by omega⟩, j)) =
        (path e inner k).denominator.coeff j.val := by
  have H := product_entries N e inner k hN he j
  rw [MatrixProduct.layeredFin_pow_apply, MatrixProduct.layeredFin_pow_apply]
  simpa only [Nat.zero_add, ite_true] using H

end LeanCanny.Algebra.SymbolicCoordinatePath
