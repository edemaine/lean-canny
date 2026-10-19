/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzCoefficients

/-!
# Linear transformations of characteristic coefficients

All coefficient vectors are padded to a common width and indexed in ascending
degree. Adding the leading row and column acts by an upper Hessenberg matrix:
one shifted diagonal, the leading scalar on the diagonal, and scalar power
moments above it. The transformation entries use only the input matrix and its
smaller principal block, not any characteristic coefficients.
-/

@[expose] public section

noncomputable section

namespace LeanCanny.Algebra.Berkowitz
open Matrix Polynomial Finset

variable {R : Type*} [CommRing R]

def coefficientKernel {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (d k : ℕ) : R :=
  (if k + 1 = d then 1 else 0) - (if k = d then A 0 0 else 0) -
    if d < k ∧ k ≤ n then
      borderMoment (fun i => A 0 i.succ) (fun i => A i.succ 0)
        (A.submatrix Fin.succ Fin.succ) (k - (d + 1))
    else 0

def transformation {n : ℕ} (w : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin w) (Fin w) R := fun d k => coefficientKernel A d.val k.val

def coefficientVector {n : ℕ} (w : ℕ) (A : Matrix (Fin n) (Fin n) R) : Fin w → R :=
  fun i => A.charpoly.coeff i.val

theorem sum_shift (f : ℕ → R) (w d : ℕ) (hd : d < w) :
    (∑ k ∈ range w, (if k + 1 = d then (1 : R) else 0) * f k) =
      if d = 0 then 0 else f (d - 1) := by
  by_cases hz : d = 0
  · simp [hz]
  · have heq (k : ℕ) : k + 1 = d ↔ k = d - 1 := by omega
    simp only [heq, ite_mul, one_mul, zero_mul]
    simp [hz, show d - 1 < w by omega]

theorem sum_kernel {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (w d : ℕ) (hn : n < w) (hd : d < w) :
    (∑ k ∈ range w, coefficientKernel A d k *
      (A.submatrix Fin.succ Fin.succ).charpoly.coeff k) = A.charpoly.coeff d := by
  let D := A.submatrix Fin.succ Fin.succ
  have hfilter : {k ∈ range w | d < k ∧ k ≤ n} = Icc (d + 1) n := by
    ext k
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  simp only [coefficientKernel, sub_mul, sum_sub_distrib]
  rw [sum_shift _ w d hd]
  have hdiag : (∑ k ∈ range w, (if k = d then A 0 0 else 0) * D.charpoly.coeff k) =
      A 0 0 * D.charpoly.coeff d := by simp [ite_mul, hd]
  have hmoment : (∑ k ∈ range w, (if d < k ∧ k ≤ n then
      borderMoment (fun i => A 0 i.succ) (fun i => A i.succ 0) D (k - (d + 1)) else 0) *
      D.charpoly.coeff k) = ∑ k ∈ Icc (d + 1) n,
        D.charpoly.coeff k *
          borderMoment (fun i => A 0 i.succ) (fun i => A i.succ 0) D (k - (d + 1)) := by
    simp only [ite_mul, zero_mul, ← sum_filter, hfilter]
    apply sum_congr rfl
    intro k _
    exact mul_comm _ _
  rw [hdiag, hmoment, charpoly_coeff_succ]

theorem transformation_mulVec {n w : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hn : n < w) :
    transformation w A *ᵥ coefficientVector w (A.submatrix Fin.succ Fin.succ) =
      coefficientVector w A := by
  funext d
  change (∑ k : Fin w, coefficientKernel A d.val k.val *
    (A.submatrix Fin.succ Fin.succ).charpoly.coeff k.val) = A.charpoly.coeff d.val
  rw [Fin.sum_univ_eq_sum_range (fun k => coefficientKernel A d.val k *
    (A.submatrix Fin.succ Fin.succ).charpoly.coeff k)]
  exact sum_kernel A w d.val hn d.isLt

end LeanCanny.Algebra.Berkowitz
