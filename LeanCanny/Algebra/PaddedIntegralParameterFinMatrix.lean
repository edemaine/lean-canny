/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCoordinateBasisFinStep
public import LeanCanny.Algebra.PaddedIntegralParameterMatrix

/-! # Actual padded generator matrices in canonical fixed-width bases

The old rank and the new scalar digit use their native finite-product
index. The last block column reads only the original coefficient matrices
and a binary power of the selected leading-coefficient matrix.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralParameterExtension
open IntegralCoordinateBasis FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] [Nontrivial A] {m B : ℕ}

theorem fin_root_matrix (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A) (d : ℕ)
    (r t : Fin (count m B)) (i j : Fin (2 ^ B)) :
    Algebra.leftMulMatrix (coordinateBasis b p d).finBasis (AdjoinRoot.root _)
      (pairIndex m B (r, i)) (pairIndex m B (t, j)) =
      if j.val + 1 < 2 ^ B then (if i.val = j.val + 1 then (if r = t then 1 else 0) else 0)
      else if d ≤ 2 ^ B ∧ 2 ^ B - d ≤ i.val then
        -(Algebra.leftMulMatrix b.finBasis (p.coeff (i.val - (2 ^ B - d))) *
          Algebra.leftMulMatrix b.finBasis (p.coeff d) ^ (d - 1 - (i.val - (2 ^ B - d)))) r t
      else 0 := by
  change Algebra.leftMulMatrix (b.step _ _ _).finBasis _ _ _ = _
  rw [finBasis_root_matrix]
  by_cases hj : j.val + 1 < 2 ^ B
  · rw [ite_eq_left hj, ite_eq_left hj]
  · rw [ite_eq_right hj, ite_eq_right hj, PaddedIntegralNormalization.coefficient_below]
    by_cases hi : d ≤ 2 ^ B ∧ 2 ^ B - d ≤ i.val
    · rw [ite_eq_left hi, ite_eq_left hi, map_mul, map_pow]
    · rw [ite_eq_right hi, ite_eq_right hi, map_zero]
      rfl

end LeanCanny.Algebra.PaddedIntegralParameterExtension
