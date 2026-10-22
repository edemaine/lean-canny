/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixKernelContraction
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Exactness from an invertible finite homotopy operator

For consecutive matrices `B D = 0`, invertibility of `H B + D J`
implies exactness at the middle vector space over a field. This operator
preserves the kernel of `D`; its restriction is injective and hence
surjective by finite dimensionality.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixHomotopyExact
open scoped Classical Matrix
-- Keep the caller's index equality instance for the determinant and inverse.
variable {K U S T : Type*} [Field K] [Fintype U] [Fintype S] [Fintype T] [DecidableEq S]

theorem vecMul_eq_zero_iff (D : Matrix S T K) (B : Matrix U S K) (H : Matrix S U K) (J : Matrix T S K)
    (hBD : B * D = 0) (hA : IsUnit (H * B + D * J).det) (v : S → K) :
    Matrix.vecMul v D = 0 ↔ ∃ w : U → K, Matrix.vecMul w B = v := by
  constructor
  · intro hv
    let A := H * B + D * J
    let E := LinearMap.ker D.vecMulLinear
    have hpres (x : E) : Matrix.vecMul (Matrix.vecMul x.val A) D = 0 := by
      have hx : Matrix.vecMul x.val D = 0 := x.property
      change Matrix.vecMul (Matrix.vecMul x.val (H * B + D * J)) D = 0
      rw [Matrix.vecMul_add, Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc, hBD,
        Matrix.mul_zero, Matrix.vecMul_zero, zero_add, ← Matrix.vecMul_vecMul,
        hx, Matrix.zero_vecMul, Matrix.zero_vecMul]
    let F : E →ₗ[K] E := (A.vecMulLinear.comp E.subtype).codRestrict E hpres
    have hinj : Function.Injective F := by
      intro x y h
      apply Subtype.ext
      have he := congrArg (fun z : E => Matrix.vecMul z.val A⁻¹) h
      change Matrix.vecMul (Matrix.vecMul x.val A) A⁻¹ = Matrix.vecMul (Matrix.vecMul y.val A) A⁻¹ at he
      simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hA, Matrix.vecMul_one] using he
    obtain ⟨w, hw⟩ := LinearMap.surjective_of_injective hinj ⟨v, hv⟩
    have he := congrArg Subtype.val hw
    change Matrix.vecMul w.val (H * B + D * J) = v at he
    rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul] at he
    have hwD : Matrix.vecMul w.val D = 0 := w.property
    rw [hwD, Matrix.zero_vecMul, add_zero] at he
    exact ⟨Matrix.vecMul w.val H, he⟩
  · rintro ⟨w, rfl⟩
    rw [Matrix.vecMul_vecMul, hBD, Matrix.vecMul_zero]

end LeanCanny.Algebra.MatrixHomotopyExact
