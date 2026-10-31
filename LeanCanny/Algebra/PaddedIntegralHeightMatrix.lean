/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralParameterFinMatrix
public import LeanCanny.Algebra.MatrixPolynomialEntryCorrect

/-! # Canonical height matrices from the selected leading-coefficient matrix

Changing to the fixed-width basis preserves the integer characteristic
polynomial. The old inverse element is obtained by matrix polynomial
evaluation. Multiplying its lifted matrix by the constructed new generator
gives the actual height-numerator multiplication matrix.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCoordinateBasis
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {m B : ℕ}

theorem finBasis_charpoly (b : IntegralCoordinateBasis A m (2 ^ B)) (x : A) :
    (Algebra.leftMulMatrix b.finBasis x).charpoly = (Algebra.leftMulMatrix b.basis x).charpoly := by
  have HM : Algebra.leftMulMatrix b.finBasis x =
      Matrix.reindex (boxEquiv m B) (boxEquiv m B) (Algebra.leftMulMatrix b.basis x) := by
    ext i j
    simp only [finBasis, Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.repr_reindex_apply,
      Module.Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [HM, Matrix.charpoly_reindex]

theorem finBasis_polynomial (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial ℤ) (x : A) :
    Algebra.leftMulMatrix b.finBasis (Polynomial.aeval x p) =
      Polynomial.aeval (Algebra.leftMulMatrix b.finBasis x) p :=
  (Polynomial.aeval_algHom_apply (Algebra.leftMulMatrix b.finBasis) x p).symm

end LeanCanny.Algebra.IntegralCoordinateBasis

namespace LeanCanny.Algebra.PaddedIntegralParameterExtension
open IntegralCoordinateBasis FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] [Nontrivial A] {m B : ℕ}

noncomputable def inverseMatrix (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A) (d : ℕ) :
    Matrix (Fin (count m B)) (Fin (count m B)) ℤ :=
  Polynomial.aeval (Algebra.leftMulMatrix b.finBasis (p.coeff d))
    (IntegralParameterInverse.inverse (Algebra.leftMulMatrix b.finBasis (p.coeff d)).charpoly)

omit [Nontrivial A] in
theorem denominator_finBasis (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A) (d : ℕ) :
    denominator b p d = IntegralParameterInverse.denominator (Algebra.leftMulMatrix b.finBasis (p.coeff d)).charpoly := by
  rw [finBasis_charpoly]
  rfl

omit [Nontrivial A] in
theorem inverseMatrix_eq (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A) (d : ℕ) :
    inverseMatrix b p d = Algebra.leftMulMatrix b.finBasis
      (Polynomial.aeval (p.coeff d) (IntegralParameterInverse.inverse (Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly)) := by
  rw [finBasis_polynomial, ← finBasis_charpoly]
  rfl

theorem numerator_matrix (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A) (d : ℕ) :
    Algebra.leftMulMatrix (coordinateBasis b p d).finBasis (numerator b p d) =
      Algebra.leftMulMatrix (coordinateBasis b p d).finBasis (AdjoinRoot.root _) *
        Algebra.leftMulMatrix (coordinateBasis b p d).finBasis (AdjoinRoot.of _
          (Polynomial.aeval (p.coeff d) (IntegralParameterInverse.inverse
            (Algebra.leftMulMatrix b.finBasis (p.coeff d)).charpoly))) := by
  rw [numerator, map_mul, finBasis_charpoly]

theorem lifted_inverse_entry (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A) (d : ℕ)
    (r t : Fin (count m B)) (i j : Fin (2 ^ B)) :
    Algebra.leftMulMatrix (coordinateBasis b p d).finBasis (AdjoinRoot.of _
      (Polynomial.aeval (p.coeff d) (IntegralParameterInverse.inverse
        (Algebra.leftMulMatrix b.finBasis (p.coeff d)).charpoly)))
      (pairIndex m B (r, i)) (pairIndex m B (t, j)) = if i = j then inverseMatrix b p d r t else 0 := by
  change Algebra.leftMulMatrix (b.step _ _ _).finBasis _ _ _ = _
  rw [finBasis_of_matrix, finBasis_polynomial]
  rfl

end LeanCanny.Algebra.PaddedIntegralParameterExtension
