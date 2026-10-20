/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayRelationBlockEquiv

/-! # The extraneous determinant divides the relation determinant

Splitting the relation matrix first by input coordinate and then by greatest
eligible coordinate identifies one diagonal factor with every extraneous
block. The remaining blocks give an explicit polynomial factor. This does
not prove divisibility of the Macaulay numerator by the extraneous determinant.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixBlockProduct
open scoped BigOperators Classical

theorem determinant {R S T : Type*} [CommRing R] [Fintype S] [DecidableEq S]
    [Fintype T] [LinearOrder T] (M : Matrix S S R) (b : S → T) (h : M.BlockTriangular b) :
    M.det = ∏ t : T, (M.toSquareBlock b t).det := by
  rw [h.det]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro t _ ht
  have : IsEmpty {s : S // b s = t} := ⟨fun s => ht (Finset.mem_image.mpr ⟨s.val, Finset.mem_univ _, s.property⟩)⟩
  exact Matrix.det_isEmpty

end LeanCanny.Algebra.MatrixBlockProduct

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem relationMinor_det_product (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (relationMinor p d W hW).det = ∏ i : Fin n, ∏ k : Fin n, (relationDoubleBlock p d W hW i k).det := by
  have h := MatrixBlockProduct.determinant (relationMinor p d W hW)
    (fun a => OrderDual.toDual a.val.1) (relationMinor_blockTriangular p d W hW)
  change (relationMinor p d W hW).det = ∏ i : Fin n, (relationCoordinateBlock p d W hW i).det at h
  rw [h]
  apply Finset.prod_congr rfl
  intro i _
  exact MatrixBlockProduct.determinant _ _ (relationCoordinateBlock_blockTriangular p d W hW i)

theorem extraneousMinor_det_product (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (extraneousMinor p d W).det = ∏ i : Fin n, ((extraneousMinor p d W).toSquareBlock (extraneousLast d W) i).det :=
  MatrixBlockProduct.determinant _ _ (extraneousMinor_blockTriangular p d W)

noncomputable def higherRelationFactor (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) : R :=
  ∏ i : Fin n, ∏ k ∈ Finset.univ.erase i, (relationDoubleBlock p d W hW i k).det

theorem relationMinor_det_eq_extraneous_mul (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (relationMinor p d W hW).det = (extraneousMinor p d W).det * higherRelationFactor p d W hW := by
  rw [relationMinor_det_product]
  calc
    _ = ∏ i : Fin n, ((relationDoubleBlock p d W hW i i).det *
        ∏ k ∈ Finset.univ.erase i, (relationDoubleBlock p d W hW i k).det) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (Finset.prod_erase_mul Finset.univ (fun k => (relationDoubleBlock p d W hW i k).det)
        (Finset.mem_univ i)).symm.trans (mul_comm _ _)
    _ = (∏ i : Fin n, (relationDoubleBlock p d W hW i i).det) * higherRelationFactor p d W hW := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ = _ := by
      rw [extraneousMinor_det_product]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact det_relationDoubleBlock_diagonal p d W hW i

theorem extraneousMinor_det_dvd_relationMinor_det (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (extraneousMinor p d W).det ∣ (relationMinor p d W hW).det :=
  ⟨higherRelationFactor p d W hW, relationMinor_det_eq_extraneous_mul p d W hW⟩

theorem relation_characteristic_eq_extraneous_mul (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (AffineCharacteristic.subtractiveMatrix (relationMinor p d W hW)).det =
      (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det *
        higherRelationFactor (subtractiveSystem p d) d W hW := by
  rw [← relationMinor_subtractiveSystem, relationMinor_det_eq_extraneous_mul, extraneousMinor_subtractiveSystem]

theorem extraneous_characteristic_dvd_relation_characteristic (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det ∣
      (AffineCharacteristic.subtractiveMatrix (relationMinor p d W hW)).det :=
  ⟨higherRelationFactor (subtractiveSystem p d) d W hW, relation_characteristic_eq_extraneous_mul p d W hW⟩

theorem higherRelationFactor_subtractive_ne_zero [IsDomain R] (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    higherRelationFactor (subtractiveSystem p d) d W hW ≠ 0 := by
  intro hz
  have h := relation_characteristic_eq_extraneous_mul p d W hW
  rw [hz, mul_zero] at h
  exact AffineCharacteristic.subtractive_det_ne_zero _ h

theorem contraction_characteristic_eq_full_extraneous_mul (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (AffineCharacteristic.subtractiveMatrix
      (fullMatrix p d W * MatrixMinorSection.rowSelection (R := R) (selectedMultiplier d W) +
        divisionRelations p d W hW)).det =
      (AffineCharacteristic.subtractiveMatrix (activeMinor p d W)).det *
        (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det *
          higherRelationFactor (subtractiveSystem p d) d W hW := by
  rw [contraction_characteristic_determinant, relation_characteristic_eq_extraneous_mul, mul_assoc]

end LeanCanny.Algebra.Macaulay
