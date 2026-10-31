/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralParameterExtension
public import LeanCanny.Algebra.MonicExtensionMatrix

/-! # Uniform-rank scalar generator matrices from original coefficients

The normalization column is shifted by N-d and zero padded. Its nonzero
blocks use the original coefficient multiplication matrices and powers of
the selected leading-coefficient matrix; no extension matrix is an input.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralParameterExtension
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] [Nontrivial A] {N : ℕ}

theorem tower_root_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ A)
    (p : Polynomial A) (d : ℕ) (i j : ι × Fin N) :
    Algebra.leftMulMatrix (b.smulTower (IntegralCoordinateBasis.relativeBasis
      (PaddedIntegralNormalization.polynomial p d N) (PaddedIntegralNormalization.monic p d N)
      (PaddedIntegralNormalization.natDegree p d N))) (AdjoinRoot.root _) i j =
      if j.2.val + 1 < N then (if i.2.val = j.2.val + 1 then (if i.1 = j.1 then 1 else 0) else 0)
      else if d ≤ N ∧ N - d ≤ i.2.val then
        -(Algebra.leftMulMatrix b (p.coeff (i.2.val - (N - d))) *
          Algebra.leftMulMatrix b (p.coeff d) ^ (d - 1 - (i.2.val - (N - d)))) i.1 j.1
      else 0 := by
  rw [IntegralCoordinateBasis.tower_root_matrix]
  by_cases hj : j.2.val + 1 < N
  · rw [ite_eq_left hj, ite_eq_left hj]
  · rw [ite_eq_right hj, ite_eq_right hj, PaddedIntegralNormalization.coefficient_below]
    by_cases hi : d ≤ N ∧ N - d ≤ i.2.val
    · rw [ite_eq_left hi, ite_eq_left hi, map_mul, map_pow]
    · rw [ite_eq_right hi, ite_eq_right hi, map_zero]
      rfl

end LeanCanny.Algebra.PaddedIntegralParameterExtension
