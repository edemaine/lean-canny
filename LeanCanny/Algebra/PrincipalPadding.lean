/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCharacteristic

/-! # Principal minors represented by identity-padded matrices

Replacing rows outside a selected finite set with identity rows preserves the
principal determinant. This representation keeps the original index space.
Affine deformation commutes with the padding, and the lowest subtractive
characteristic coefficient agrees with that of the actual principal minor.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrincipalPadding
open scoped Classical

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]

noncomputable def matrix (A : Matrix ι ι R) (s : Finset ι) : Matrix ι ι R :=
  fun r c => if r ∈ s then A r c else (1 : Matrix ι ι R) r c

theorem determinant (A : Matrix ι ι R) (s : Finset ι) :
    (matrix A s).det = (A.submatrix (fun i : s => i.val) (fun i : s => i.val)).det := by
  have h : matrix A s = Matrix.of (s.piecewise A.row (1 : Matrix ι ι R).row) := by
    funext r c
    by_cases hr : r ∈ s <;> simp [matrix, Finset.piecewise, hr]
  rw [h]
  exact Matrix.det_piecewise_one_eq_submatrix_det A s

omit [Fintype ι] in
theorem matrix_one (s : Finset ι) : matrix (1 : Matrix ι ι R) s = 1 := by
  funext r c
  simp only [matrix, ite_self]

omit [Fintype ι] in
theorem matrix_map (φ : R →+* S) (A : Matrix ι ι R) (s : Finset ι) :
    (matrix A s).map φ = matrix (A.map φ) s := by
  funext r c
  by_cases hrc : r = c
  · subst c
    by_cases hr : r ∈ s <;> simp [matrix, hr]
  · by_cases hr : r ∈ s <;> simp [matrix, hr, hrc]

omit [Fintype ι] in
theorem matrix_affine (A : Matrix ι ι R) (s : Finset ι) :
    matrix (AffineCharacteristic.affineMatrix A) s = AffineCharacteristic.affineMatrix (matrix A s) := by
  funext r c
  by_cases hrc : r = c
  · subst c
    by_cases hr : r ∈ s <;> simp [matrix, AffineCharacteristic.affineMatrix, hr]
  · by_cases hr : r ∈ s <;> simp [matrix, AffineCharacteristic.affineMatrix, hr, hrc]

omit [Fintype ι] in
theorem affine_submatrix (A : Matrix ι ι R) (s : Finset ι) :
    (AffineCharacteristic.affineMatrix A).submatrix (fun i : s => i.val) (fun i : s => i.val) =
      AffineCharacteristic.affineMatrix (A.submatrix (fun i : s => i.val) (fun i : s => i.val)) := by
  funext r c
  by_cases hrc : r = c
  · subst c
    simp [AffineCharacteristic.affineMatrix]
  · have hval : r.val ≠ c.val := fun h => hrc (Subtype.ext h)
    simp [AffineCharacteristic.affineMatrix, hrc, hval]

theorem affine_determinant (A : Matrix ι ι R) (s : Finset ι) :
    (AffineCharacteristic.affineMatrix (matrix A s)).det =
      (AffineCharacteristic.affineMatrix (A.submatrix (fun i : s => i.val) (fun i : s => i.val))).det := by
  rw [← matrix_affine, determinant, affine_submatrix]

theorem characteristic_lowest (A : Matrix ι ι R) (s : Finset ι) :
    (AffineCharacteristic.subtractiveMatrix (matrix A s)).det.natTrailingDegree =
      (AffineCharacteristic.subtractiveMatrix (A.submatrix (fun i : s => i.val) (fun i : s => i.val))).det.natTrailingDegree ∧
    (AffineCharacteristic.subtractiveMatrix (matrix A s)).det.trailingCoeff =
      (AffineCharacteristic.subtractiveMatrix (A.submatrix (fun i : s => i.val) (fun i : s => i.val))).det.trailingCoeff := by
  have hp := AffineCharacteristic.subtractive_lowest (matrix A s)
  have hm := AffineCharacteristic.subtractive_lowest (A.submatrix (fun i : s => i.val) (fun i : s => i.val))
  rw [affine_determinant] at hp
  exact ⟨hp.1.trans hm.1.symm, hp.2.trans hm.2.symm⟩

end LeanCanny.Algebra.PrincipalPadding
