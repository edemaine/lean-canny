/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # A section from an invertible selected row minor

The inverse of a selected square matrix followed by the row selector is an
explicit section of the full rectangular row-vector map. The determinant
condition is a unit condition over a commutative ring.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixMinorSection
open scoped Matrix
variable {R S T : Type*} [CommRing R] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

noncomputable def rowSelection (f : T → S) : Matrix T S R := (1 : Matrix S S R).submatrix f id

omit [Fintype T] [DecidableEq T] in
theorem rowSelection_mul (M : Matrix S T R) (f : T → S) :
    rowSelection f * M = M.submatrix f id :=
  Matrix.one_submatrix_mul f (Equiv.refl S) M

noncomputable def sectionMatrix (M : Matrix S T R) (f : T → S) : Matrix T S R :=
  (M.submatrix f id)⁻¹ * rowSelection f

theorem sectionMatrix_mul (M : Matrix S T R) (f : T → S) (h : IsUnit (M.submatrix f id).det) :
    sectionMatrix M f * M = 1 := by
  rw [sectionMatrix, Matrix.mul_assoc, rowSelection_mul, Matrix.nonsing_inv_mul _ h]

theorem vecMul_section (M : Matrix S T R) (f : T → S) (h : IsUnit (M.submatrix f id).det) (w : T → R) :
    Matrix.vecMul (Matrix.vecMul w (sectionMatrix M f)) M = w := by
  rw [Matrix.vecMul_vecMul, sectionMatrix_mul M f h, Matrix.vecMul_one]

theorem vecMul_surjective (M : Matrix S T R) (f : T → S) (h : IsUnit (M.submatrix f id).det) :
    Function.Surjective (Matrix.vecMul · M) := by
  intro w
  exact ⟨Matrix.vecMul w (sectionMatrix M f), vecMul_section M f h w⟩

end LeanCanny.Algebra.MatrixMinorSection
