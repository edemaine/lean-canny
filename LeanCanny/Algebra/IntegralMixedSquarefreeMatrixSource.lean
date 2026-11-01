/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCoordinateMatrixSource

/-! # Actual PSC determinant source for selected squarefree cuts

After the bounded nilpotent substitution, a squarefree exceptional factor
is the original coordinate leading times one literal fixed-bound PSC
determinant. Its entries request coefficients of the SAME relative
coordinate polynomial and its derivative. No component-selection test or
absolute norm is part of this arithmetic identity.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeMatrixSource
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCoordinateSquarefree
open Polynomial PrincipalSubresultant
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def coordinateImage (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) :=
  (coordinate x hm r j).map (AdjoinRoot.mk (X ^ (2 ^ B)))

noncomputable def matrix (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (coordinateDegree P r)) :=
  subresultantMatrix (coordinateImage x hm r j) (coordinateImage x hm r j).derivative
    (coordinateDegree P r) (coordinateDegree P r - 1) i.val

theorem nilpotent_value (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (coordinateDegree P r)) :
    IntegralMixedCutNilpotent.value x hm r (.squarefree j i) =
      (coordinateImage x hm r j).coeff (coordinateDegree P r) * (matrix x hm r j i).det := by
  change AdjoinRoot.mk _ ((coordinate x hm r j).coeff (coordinateDegree P r) *
    psc (coordinate x hm r j) (coordinate x hm r j).derivative
      (coordinateDegree P r) (coordinateDegree P r - 1) i.val) = _
  rw [map_mul, ← Polynomial.coeff_map, ← psc_map_map, ← Polynomial.derivative_map]
  change (coordinateImage x hm r j).coeff (coordinateDegree P r) *
    psc (coordinateImage x hm r j) (coordinateImage x hm r j).derivative
      (coordinateDegree P r) (coordinateDegree P r - 1) i.val = _
  rw [psc_def]
  rfl

theorem matrix_size (P : SpatialSource n) (r : Rule n) (i : Fin (coordinateDegree P r)) :
    Fintype.card (Fin (coordinateDegree P r + (coordinateDegree P r - 1) - 2 * i.val)) ≤
      2 * coordinateDegree P r := by
  rw [Fintype.card_fin]
  omega

theorem nilpotent_matrix (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (coordinateDegree P r)) :
    Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis
      (IntegralMixedCutNilpotent.value x hm r (.squarefree j i)) =
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis
        ((coordinateImage x hm r j).coeff (coordinateDegree P r)) *
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis ((matrix x hm r j i).det) := by
  rw [nilpotent_value, map_mul]

end LeanCanny.Algebra.IntegralMixedSquarefreeMatrixSource
