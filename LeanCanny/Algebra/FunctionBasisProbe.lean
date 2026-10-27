/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FunctionBasisPencil
public import Mathlib.Basic.Sign.Basic

/-! # Recovering one feature from a separating weighted Gram function

At a value v(x), the linear coefficient of det(v(x)G-H+U S) is s(x)
times the corresponding coefficient for S=G. Separation and a nonsingular
basis make the latter coefficient nonzero. Multiplying their signs recovers
the sign of s(x), without computing a matrix inverse or a kernel vector.
-/

@[expose] public section
namespace LeanCanny.Algebra.FunctionBasisProbe
open Polynomial FunctionBasisPencil
open scoped Classical BigOperators

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

noncomputable def matrix (A : Matrix ι ι R) (v s : ι → R) (h : R) : Matrix ι ι R[X] :=
  fun i j => C (h * gram A i j - weighted A v i j) + C (weighted A s i j) * X

theorem factor (A : Matrix ι ι R) (v s : ι → R) (h : R) :
    matrix A v s h = A.map C * Matrix.diagonal (fun i => C (h - v i) + C (s i) * X) * (A.map C).transpose := by
  apply Matrix.ext
  intro i j
  have hg : gram A i j = ∑ k, A i k * A j k := rfl
  have hw (w : ι → R) : weighted A w i j = ∑ k, A i k * w k * A j k := by
    unfold weighted
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  have hr : (A.map C * Matrix.diagonal (fun i => C (h - v i) + C (s i) * (X : R[X])) * (A.map C).transpose) i j =
      ∑ k, C (A i k) * (C (h - v k) + C (s k) * X) * C (A j k) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.map_apply, Matrix.transpose_apply]
  rw [matrix, hg, hw, hw, hr]
  simp only [map_sub, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem determinant (A : Matrix ι ι R) (v s : ι → R) (h : R) :
    (matrix A v s h).det = C (gram A).det * ∏ i, (C (h - v i) + C (s i) * X) := by
  have hd : (A.map (C : R →+* R[X])).det = C A.det := (C.map_det A).symm
  rw [factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose,
    hd, gram, Matrix.det_mul, Matrix.det_transpose, map_mul]
  ring

theorem coefficient_one (A : Matrix ι ι R) (v s : ι → R) (x : ι) :
    (matrix A v s (v x)).det.coeff 1 = (gram A).det * s x * ∏ j ∈ Finset.univ.erase x, (v x - v j) := by
  rw [determinant, ← Finset.mul_prod_erase Finset.univ (fun i => C (v x - v i) + C (s i) * X) (Finset.mem_univ x)]
  simp only [sub_self, C_0, zero_add]
  rw [mul_assoc (C (s x)) X]
  simp only [coeff_C_mul, coeff_X_mul, coeff_zero_prod, coeff_add, coeff_C_zero, coeff_mul_X_zero, add_zero]
  ring

theorem coefficient_ratio (A : Matrix ι ι R) (v s : ι → R) (x : ι) :
    (matrix A v s (v x)).det.coeff 1 = s x * (matrix A v (fun _ => 1) (v x)).det.coeff 1 := by
  rw [coefficient_one, coefficient_one]
  ring

variable [IsDomain R]

theorem denominator_nonzero (A : Matrix ι ι R) (v : ι → R) (x : ι)
    (hA : A.det ≠ 0) (hv : Function.Injective v) : (matrix A v (fun _ => 1) (v x)).det.coeff 1 ≠ 0 := by
  rw [coefficient_one, mul_one]
  apply mul_ne_zero
  · rw [gram, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hA hA
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro he
    exact (Finset.mem_erase.mp hj).1 (hv he).symm

variable [LinearOrder R] [IsStrictOrderedRing R]

omit [IsDomain R] in
theorem sign_ratio (A : Matrix ι ι R) (v s : ι → R) (x : ι)
    (hA : A.det ≠ 0) (hv : Function.Injective v) :
    SignType.sign ((matrix A v s (v x)).det.coeff 1) *
      SignType.sign ((matrix A v (fun _ => 1) (v x)).det.coeff 1) = SignType.sign (s x) := by
  have hd := denominator_nonzero A v x hA hv
  have hs : SignType.sign ((matrix A v (fun _ => 1) (v x)).det.coeff 1) *
      SignType.sign ((matrix A v (fun _ => 1) (v x)).det.coeff 1) = 1 := by
    rw [← sign_mul]
    exact sign_eq_one_iff.mpr (mul_self_pos.mpr hd)
  rw [coefficient_ratio, sign_mul, mul_assoc, hs, mul_one]

end LeanCanny.Algebra.FunctionBasisProbe
