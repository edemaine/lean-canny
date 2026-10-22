/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayHomotopyBridge

/-! # Concrete determinant factors of the finite homotopy operator

In exterior degree one, the canonical operator `H D + D H` reindexes to
the existing full Macaulay source contraction. Its determinant is the
Macaulay numerator times the complementary relation determinant. The known
relation factorization gives an extraneous factor in this same operator.
Divisibility of the numerator by the extraneous determinant is not asserted.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem contractionMatrix_zero_reindex (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (contractionMatrix p d W hp hW 0).submatrix (macaulaySourceEquiv d W) (macaulaySourceEquiv d W) =
      Macaulay.fullMatrix p d W * MatrixMinorSection.rowSelection (Macaulay.selectedMultiplier d W) +
        Macaulay.divisionRelations p d W hW := by
  unfold contractionMatrix
  rw [Matrix.submatrix_add]
  change (homotopyMatrix (R := R) d W hW 1 * canonicalMatrix p d (Macaulay.level d) W hp hW 1).submatrix
      (macaulaySourceEquiv d W) (macaulaySourceEquiv d W) +
    (canonicalMatrix p d (Macaulay.level d) W hp hW 0 * homotopyMatrix (R := R) d W hW 0).submatrix
      (macaulaySourceEquiv d W) (macaulaySourceEquiv d W) = _
  rw [homotopyMatrix_one_differential_macaulay p d W hp hW]
  have hm := Matrix.submatrix_mul_equiv (canonicalMatrix p d (Macaulay.level d) W hp hW 0)
    (homotopyMatrix (R := R) d W hW 0) (macaulaySourceEquiv d W) (macaulayTargetEquiv d W) (macaulaySourceEquiv d W)
  have hd : (canonicalMatrix p d (Macaulay.level d) W hp hW 0).submatrix
      (macaulaySourceEquiv d W) (macaulayTargetEquiv d W) = Macaulay.fullMatrix p d W :=
    canonicalMatrix_macaulay p d W hp hW
  rw [hd, homotopyMatrix_zero_macaulay] at hm
  rw [← hm, add_comm]

theorem contractionMatrix_zero_determinant (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (contractionMatrix p d W hp hW 0).det = (Macaulay.activeMinor p d W).det *
      (Macaulay.relationMinor p d W hW).det := by
  have h := congrArg Matrix.det (contractionMatrix_zero_reindex p d W hp hW)
  rw [Matrix.det_submatrix_equiv_self] at h
  exact h.trans (Macaulay.contraction_determinant p d W hW)

theorem contractionMatrix_zero_full_factor (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (contractionMatrix p d W hp hW 0).det = (Macaulay.activeMinor p d W).det *
      (Macaulay.extraneousMinor p d W).det * Macaulay.higherRelationFactor p d W hW := by
  rw [contractionMatrix_zero_determinant p d W hp hW, Macaulay.relationMinor_det_eq_extraneous_mul, mul_assoc]

theorem contractionMatrix_zero_characteristic_factor (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (AffineCharacteristic.subtractiveMatrix (contractionMatrix p d W hp hW 0)).det =
      (AffineCharacteristic.subtractiveMatrix (Macaulay.activeMinor p d W)).det *
        (AffineCharacteristic.subtractiveMatrix (Macaulay.extraneousMinor p d W)).det *
          Macaulay.higherRelationFactor (Macaulay.subtractiveSystem p d) d W hW := by
  rw [← contractionMatrix_subtractiveSystem p d W hp hW 0,
    contractionMatrix_zero_full_factor (Macaulay.subtractiveSystem p d) d W
      (Macaulay.subtractiveSystem_homogeneous p d hp) hW,
    Macaulay.activeMinor_subtractiveSystem, Macaulay.extraneousMinor_subtractiveSystem]

end LeanCanny.Algebra.KoszulWeighted
