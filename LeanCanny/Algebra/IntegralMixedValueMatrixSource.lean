/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCutNilpotent

/-! # Actual relative Gram coefficient source for equation-value cuts

The fixed reciprocal Macaulay Gram matrix is displayed over the old
algebra and sweep parameter. After nilpotent substitution the chosen
value cut is one reversed determinant coefficient. The zero coefficient
case is kept explicitly. Neither a supplied eliminant nor an absolute
integer norm occurs in this source identity.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueMatrixSource
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCoordinateSquarefree
open IntegralMixedGridValue IntegralMixedExceptionalBounds Polynomial ProjectiveGramEliminant
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def matrix (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) :=
  gram (MacaulayFullBox.matrix
    (RelativeProjectiveValueGram.system
      (AffineRingCoordinates.homogeneousRows (RelativeAffineGridValueGram.rows (coordinate x hm r))
        (fun _ => coordinateDegree P r))
      (RelativeAffineGridValueGram.test (IntegralMixedSweepRows.row x hm r i) P.degree) P.degree)
    (RelativeProjectiveValueGram.degrees (fun _ : Fin (n - r.critical.offset.val + 1) => coordinateDegree P r) P.degree)
    (IntegralMixedGridValue.width P r))

theorem polynomial_eq (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) :
    polynomial x hm r i = X * (matrix x hm r i).det.reflect (IntegralMixedGridValue.dimension P r) := rfl

noncomputable def nilpotentMatrix (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) :=
  (matrix x hm r i).map (Polynomial.mapRingHom (AdjoinRoot.mk (X ^ (2 ^ B))))

theorem nilpotent_value_zero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) :
    IntegralMixedCutNilpotent.value x hm r (.value i 0) = 0 := by
  change AdjoinRoot.mk _ ((polynomial x hm r i).coeff 0) = 0
  rw [polynomial_eq, Polynomial.coeff_X_mul_zero, map_zero]

theorem nilpotent_value_succ (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (k : ℕ) (hk : k ≤ IntegralMixedGridValue.dimension P r) :
    IntegralMixedCutNilpotent.value x hm r
      (.value i ⟨k + 1, by change k + 1 < IntegralMixedGridValue.dimension P r + 2; omega⟩) =
        (nilpotentMatrix x hm r i).det.coeff (IntegralMixedGridValue.dimension P r - k) := by
  change AdjoinRoot.mk _ ((polynomial x hm r i).coeff (k + 1)) = _
  rw [polynomial_eq, Polynomial.coeff_X_mul, Polynomial.coeff_reflect, Polynomial.revAt_le hk]
  have HE : (nilpotentMatrix x hm r i).det =
      (matrix x hm r i).det.map (AdjoinRoot.mk (X ^ (2 ^ B))) :=
    (RingHom.map_det (Polynomial.mapRingHom (AdjoinRoot.mk (X ^ (2 ^ B)))) _).symm
  rw [HE, Polynomial.coeff_map]

theorem matrix_size_le (P : SpatialSource n) (r : Rule n) :
    Fintype.card (MacaulayFullBox.Column (n - r.critical.offset.val + 1 + 1) (IntegralMixedGridValue.width P r)) ≤
      valueDimension (n + 1) P.degree := by
  have HL : FixedWidthPolynomial.count (n - r.critical.offset.val + 1 + 1) (IntegralMixedGridValue.width P r) ≤
      IntegralMixedGridValue.dimension P r :=
    Nat.le_mul_of_pos_left _ (by omega)
  simpa only [Fintype.card_fin] using HL.trans (value_dimension_le P r)

end LeanCanny.Algebra.IntegralMixedValueMatrixSource
