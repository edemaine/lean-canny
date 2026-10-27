/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators

/-! # Recovering function values from weighted Gram entries

If rows of A describe a function basis, G = A Aᵀ is its Gram matrix and
H = A diag(v) Aᵀ contains weighted moments. The polynomial det(TG-H) is
det(G) times the product of T-v(x). Thus distinct-root counting tests whether
the function v separates the underlying finite set, without constructing
G's inverse. The factorization itself needs no invertibility assumption.
-/

@[expose] public section
namespace LeanCanny.Algebra.FunctionBasisPencil
open Polynomial
open scoped Classical BigOperators

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

noncomputable def gram (A : Matrix ι ι R) : Matrix ι ι R := A * A.transpose
noncomputable def weighted (A : Matrix ι ι R) (v : ι → R) : Matrix ι ι R :=
  A * Matrix.diagonal v * A.transpose
noncomputable def pencil (A : Matrix ι ι R) (v : ι → R) : Matrix ι ι R[X] :=
  fun i j => C (gram A i j) * X - C (weighted A v i j)

theorem factor (A : Matrix ι ι R) (v : ι → R) :
    pencil A v = A.map C * Matrix.diagonal (fun i => X - C (v i)) * (A.map C).transpose := by
  apply Matrix.ext
  intro i j
  have hg : gram A i j = ∑ k, A i k * A j k := rfl
  have hw : weighted A v i j = ∑ k, A i k * v k * A j k := by
    unfold weighted
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  have hr : (A.map C * Matrix.diagonal (fun i => (X : R[X]) - C (v i)) * (A.map C).transpose) i j =
      ∑ k, C (A i k) * (X - C (v k)) * C (A j k) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.map_apply, Matrix.transpose_apply]
  rw [hr, pencil, hg, hw]
  simp only [map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [map_mul]
  ring

theorem determinant (A : Matrix ι ι R) (v : ι → R) :
    (pencil A v).det = C (gram A).det * ∏ i, (X - C (v i)) := by
  have hd : (A.map (C : R →+* R[X])).det = C A.det := (C.map_det A).symm
  rw [factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose,
    hd, gram, Matrix.det_mul, Matrix.det_transpose, map_mul]
  ring

variable [IsDomain R]

theorem nonzero (A : Matrix ι ι R) (v : ι → R) (hA : A.det ≠ 0) : (pencil A v).det ≠ 0 := by
  rw [determinant]
  apply mul_ne_zero
  · apply C_ne_zero.mpr
    rw [gram, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hA hA
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => (monic_X_sub_C (v i)).ne_zero)

theorem roots (A : Matrix ι ι R) (v : ι → R) (hA : A.det ≠ 0) :
    (pencil A v).det.roots = Finset.univ.val.map v := by
  have hg : (gram A).det ≠ 0 := by
    rw [gram, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hA hA
  rw [determinant, roots_C_mul _ hg]
  have he : (∏ i, (X - C (v i))) = (Finset.univ.val.map (fun i => X - C (v i))).prod := rfl
  rw [he]
  have hm : Finset.univ.val.map (fun i => (X : R[X]) - C (v i)) =
      (Finset.univ.val.map v).map (fun z => X - C z) := by rw [Multiset.map_map]; rfl
  rw [hm, roots_multiset_prod_X_sub_C]

variable [DecidableEq R]

theorem rootSet (A : Matrix ι ι R) (v : ι → R) (hA : A.det ≠ 0) :
    (pencil A v).det.roots.toFinset = Finset.univ.image v := by
  rw [roots A v hA]
  rfl

theorem rootCount_eq_card_iff (A : Matrix ι ι R) (v : ι → R) (hA : A.det ≠ 0) :
    (pencil A v).det.roots.toFinset.card = Fintype.card ι ↔ Function.Injective v := by
  rw [rootSet A v hA, ← Finset.card_univ, Finset.card_image_iff]
  simpa only [Finset.coe_univ] using (Set.injOn_univ : Set.InjOn v Set.univ ↔ Function.Injective v)

end LeanCanny.Algebra.FunctionBasisPencil
