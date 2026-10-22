/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-! # Determinants of conjugate maps in specified finite bases -/

@[expose] public section

namespace LeanCanny.Algebra.MatrixBasisConjugate
open scoped Classical Matrix
variable {R M N I J : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem determinant (b : Module.Basis I R M) (c : Module.Basis J R N) (e : M ≃ₗ[R] N)
    (f : M →ₗ[R] M) :
    (LinearMap.toMatrix c c (e.toLinearMap.comp (f.comp e.symm.toLinearMap))).det =
      (LinearMap.toMatrix b b f).det := by
  rw [LinearMap.toMatrix_comp c b c, LinearMap.toMatrix_comp c b b, ← Matrix.mul_assoc]
  apply Matrix.det_conj_of_mul_eq_one
  · rw [← LinearMap.toMatrix_comp, LinearEquiv.comp_coe, e.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix_id]
  · rw [← LinearMap.toMatrix_comp, LinearEquiv.comp_coe, e.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix_id]

end LeanCanny.Algebra.MatrixBasisConjugate
