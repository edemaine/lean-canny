/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UnivariateRationalCompositionWith
public import Mathlib.Data.Matrix.Basic

/-! # Fixed-exponent substitution as a coefficient matrix

The matrix is padded to any width greater than the clearing exponent. One
row-vector multiplication gives every retained output coefficient, without
an exact source-degree computation.
-/

@[expose] public section

namespace LeanCanny.Algebra.UnivariateRational
open Polynomial

noncomputable def clearingMatrix (N e : ℕ) (n d : ℤ[X]) : Matrix (Fin N) (Fin N) ℤ :=
  fun i j => if i.val ≤ e then (n ^ i.val * d ^ (e - i.val)).coeff j.val else 0

theorem vecMul_clearingMatrix (N e : ℕ) (p n d : ℤ[X]) (he : e < N) (j : Fin N) :
    Matrix.vecMul (fun k : Fin N => p.coeff k.val) (clearingMatrix N e n d) j = (clear e p n d).coeff j.val := by
  change (∑ k : Fin N, p.coeff k.val * (if k.val ≤ e then (n ^ k.val * d ^ (e - k.val)).coeff j.val else 0)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun k => p.coeff k * (if k ≤ e then (n ^ k * d ^ (e - k)).coeff j.val else 0)) N, clear_coeff]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hs : (Finset.range N).filter (fun k => k ≤ e) = Finset.range (e + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hs]

end LeanCanny.Algebra.UnivariateRational
