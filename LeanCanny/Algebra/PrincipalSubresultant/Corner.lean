/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: LinearAlgebra/Matrix/CornerMinor.lean.
Changes: selected algebraic proof slice, project namespace, and pinned Mathlib
compatibility. See STURM_SOURCES.md.
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! # Algebraic principal subresultant identities

Adapted proof slice for the signed determinant formula used in Sturm–Tarski queries.
See STURM_SOURCES.md for the upstream source and omitted material.
-/

public section

namespace LeanCanny.Algebra.PrincipalSubresultant

open Polynomial Matrix List

section
variable {n : ℕ} {R : Type*} [CommRing R]

/-- Laplace expansion along the last row of a matrix whose last row vanishes off the diagonal. -/
theorem det_eq_mul_det_submatrix_castSucc_of_row (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ j, j ≠ Fin.last n → A (Fin.last n) j = 0) :
    A.det = A (Fin.last n) (Fin.last n) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row A (Fin.last n),
    Finset.sum_eq_single (Fin.last n) (fun j _ hj => by rw [h j hj]; ring) (by simp)]
  rw [Fin.succAbove_last, Fin.val_last, Even.neg_one_pow ⟨n, rfl⟩, one_mul]

end

end LeanCanny.Algebra.PrincipalSubresultant
