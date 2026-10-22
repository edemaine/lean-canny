/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalPadding
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # The exact characteristic factor introduced by identity padding

Each omitted identity row contributes one factor of `1-X` to the subtractive
characteristic determinant. This factor has constant coefficient one.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrincipalPadding
open scoped BigOperators Classical

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem subtractive_matrix (A : Matrix ι ι R) (s : Finset ι) :
    AffineCharacteristic.subtractiveMatrix (matrix A s) =
      fun r t => (if r ∈ s then 1 else (1 - Polynomial.X : Polynomial R)) *
        matrix (AffineCharacteristic.subtractiveMatrix A) s r t := by
  funext r t
  by_cases hr : r ∈ s
  · simp only [AffineCharacteristic.subtractiveMatrix, matrix, hr, ite_true, one_mul]
  · by_cases hrt : r = t
    · subst t
      simp [AffineCharacteristic.subtractiveMatrix, matrix, hr]
    · simp [AffineCharacteristic.subtractiveMatrix, matrix, hr, hrt]

theorem subtractive_determinant (A : Matrix ι ι R) (s : Finset ι) :
    (AffineCharacteristic.subtractiveMatrix (matrix A s)).det =
      (1 - Polynomial.X : Polynomial R) ^ (sᶜ).card *
        (AffineCharacteristic.subtractiveMatrix (A.submatrix (fun i : s => i.val) (fun i : s => i.val))).det := by
  rw [subtractive_matrix]
  change (Matrix.of (fun r t : ι => (if r ∈ s then (1 : Polynomial R) else 1 - Polynomial.X) *
    (matrix (AffineCharacteristic.subtractiveMatrix A) s : Matrix ι ι (Polynomial R)) r t)).det = _
  rw [Matrix.det_mul_column, determinant]
  have hp : (∏ r : ι, if r ∈ s then (1 : Polynomial R) else 1 - Polynomial.X) =
      (1 - Polynomial.X : Polynomial R) ^ (sᶜ).card := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
    have he : Finset.univ.filter (fun r : ι => r ∉ s) = sᶜ := by
      ext r
      simp
    rw [he]
  rw [hp]
  congr 1
  apply congrArg Matrix.det
  funext r t
  by_cases hrt : r = t
  · subst t
    simp [AffineCharacteristic.subtractiveMatrix]
  · have hval : r.val ≠ t.val := fun h => hrt (Subtype.ext h)
    simp [AffineCharacteristic.subtractiveMatrix, hrt, hval]

end LeanCanny.Algebra.PrincipalPadding
