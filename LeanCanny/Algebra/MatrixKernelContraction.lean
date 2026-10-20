/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Kernel exactness from two invertible contraction matrices

If `E*D=0`, and both `D*H+E` and `H*D` are invertible, every left-kernel
vector of `D` is a row combination of `E`. This finite matrix criterion will
transport a coordinate-power Koszul contraction to a generic shifted system.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixKernelContraction
open scoped Matrix
variable {R S T : Type*} [CommRing R] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

theorem vecMul_eq_zero_iff (D : Matrix S T R) (E : Matrix S S R) (H : Matrix T S R)
    (hED : E * D = 0) (hsource : IsUnit (D * H + E).det) (htarget : IsUnit (H * D).det)
    (v : S → R) : Matrix.vecMul v D = 0 ↔ ∃ w : S → R, Matrix.vecMul w E = v := by
  constructor
  · intro hv
    let A := D * H + E
    let w := Matrix.vecMul v A⁻¹
    have hw : Matrix.vecMul w A = v := by
      change Matrix.vecMul (Matrix.vecMul v A⁻¹) A = v
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul A hsource, Matrix.vecMul_one]
    have hAD : A * D = D * (H * D) := by
      change (D * H + E) * D = D * (H * D)
      rw [Matrix.add_mul, Matrix.mul_assoc, hED, add_zero]
    have hz : Matrix.vecMul (Matrix.vecMul w D) (H * D) = 0 := by
      rw [Matrix.vecMul_vecMul, ← hAD, ← Matrix.vecMul_vecMul, hw, hv]
    have hwD : Matrix.vecMul w D = 0 := by
      have he := congrArg (fun z => Matrix.vecMul z (H * D)⁻¹) hz
      simpa only [Matrix.vecMul_vecMul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ htarget, Matrix.mul_one,
        Matrix.vecMul_one, Matrix.zero_vecMul] using he
    refine ⟨w, ?_⟩
    change Matrix.vecMul w (D * H + E) = v at hw
    rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, hwD, Matrix.zero_vecMul, zero_add] at hw
    exact hw
  · rintro ⟨w, rfl⟩
    rw [Matrix.vecMul_vecMul, hED, Matrix.vecMul_zero]

end LeanCanny.Algebra.MatrixKernelContraction
