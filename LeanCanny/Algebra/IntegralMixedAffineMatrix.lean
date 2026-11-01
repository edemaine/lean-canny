/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedAffineCoefficients
/-! # Multiplication entries of the literal affine height expressions -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedAffineMatrix
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralMixedHistory IntegralMixedAffineCoefficients
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem entry (x : State P S B m ι) (e : AffineExpr)
    (r t : Fin (FixedWidthPolynomial.count m B)) :
    Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (expression x e) r t =
      (commonDenominator x * constantCoefficient e) * (if r = t then 1 else 0) +
      ∑ i : Fin m, referenceCoefficient e i.val *
        Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (cleared x i) r t := by
  let _ := x.sampler.scalarPrefix.ring
  rw [expression_linear, map_add, map_intCast, map_sum]
  simp only [map_zsmul]
  simp only [Matrix.add_apply, Matrix.intCast_apply, Int.cast_id, Matrix.sum_apply,
    Matrix.smul_apply]
  simp only [zsmul_eq_mul, Int.cast_id]
  split_ifs <;> simp only [mul_one, mul_zero]

end LeanCanny.Algebra.IntegralMixedAffineMatrix
