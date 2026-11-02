/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSquarefreeMatrixSource
/-! # The coordinate leading factor in a squarefree cut is an integer

This identity removes a general old-algebra matrix convolution from the
squarefree reader: its first factor is a scalar identity matrix.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeLeading
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCoordinateSquarefree
open IntegralMixedSquarefreeMatrixSource Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def integer (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) : ℤ :=
  IntegralMixedCoordinateMatrixSource.leading x hm r ^
    ((PurePowerReductionBounds.bound (n - r.critical.offset.val + 1) P.degree + 1) * coordinateDegree P r)

theorem coordinate_top (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) :
    (coordinate x hm r j).coeff (coordinateDegree P r) =
      (integer x hm r : Polynomial x.sampler.scalarPrefix.carrier) := by
  rw [IntegralMixedCoordinateMatrixSource.coordinate_eq, ScaledGradedReductionAnnihilator.coefficient]
  have H := (Matrix.charpoly_monic (IntegralMixedCoordinateMatrixSource.action x hm r j)).coeff_natDegree
  have HE : (IntegralMixedCoordinateMatrixSource.action x hm r j).charpoly.coeff (coordinateDegree P r) = 1 := by
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using H
  rw [HE, one_mul]
  simp only [integer, Int.cast_pow]

theorem image_top (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) :
    (coordinateImage x hm r j).coeff (coordinateDegree P r) =
      (integer x hm r : AdjoinRoot (X ^ (2 ^ B) : Polynomial x.sampler.scalarPrefix.carrier)) := by
  rw [coordinateImage, Polynomial.coeff_map, coordinate_top, map_intCast]

theorem nilpotent_scalar (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (coordinateDegree P r)) :
    IntegralMixedCutNilpotent.value x hm r (.squarefree j i) =
      (integer x hm r : AdjoinRoot (X ^ (2 ^ B) : Polynomial x.sampler.scalarPrefix.carrier)) *
        (matrix x hm r j i).det := by
  rw [nilpotent_value, image_top]

theorem matrix_scalar (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (coordinateDegree P r)) :
    Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis
      (IntegralMixedCutNilpotent.value x hm r (.squarefree j i)) =
      integer x hm r • Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis
        (matrix x hm r j i).det := by
  rw [nilpotent_scalar]
  change (Algebra.leftMulMatrix _) ((algebraMap ℤ _) (integer x hm r) * _) = _
  rw [map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

end LeanCanny.Algebra.IntegralMixedSquarefreeLeading
