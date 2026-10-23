/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulGenericContraction
public import LeanCanny.Algebra.MatrixHomotopyExact
public import LeanCanny.Algebra.FiniteComplexTransport
public import LeanCanny.Algebra.MacaulayCanonicalMatrix

/-! # Higher exactness of the finite generic shifted Koszul complex

Characteristic invertibility of the finite homotopy operator gives
exactness of the canonical differential matrices in every positive degree.
Canonical coordinates transfer this result to the actual finite weighted
Koszul differential maps.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem canonicalMatrix_vecMul_coordinates (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ)
    (x : space (R := R) d L W (k + 1)) :
    Matrix.vecMul ((canonicalBasis (R := R) d L W (k + 1)).equivFun x) (canonicalMatrix p d L W hp hW k) =
      (canonicalBasis (R := R) d L W k).equivFun (differential p d L W hp hW k x) := by
  rw [canonicalMatrix, Matrix.vecMul_transpose]
  exact LinearMap.toMatrix_mulVec_repr _ _ _ x

theorem weighted_surjective_iff_matrix (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ) :
    Function.Surjective (differential p d L W hp hW k) ↔
      Function.Surjective (fun v => Matrix.vecMul v (canonicalMatrix p d L W hp hW k)) :=
  FiniteComplexTransport.surjective_iff_of_coordinates _
    (canonicalMatrix p d L W hp hW k).vecMulLinear
    (canonicalBasis d L W k).equivFun (canonicalBasis d L W (k + 1)).equivFun
    (canonicalMatrix_vecMul_coordinates p d L W hp hW k)

section Field
variable {K : Type*} [Field K]

theorem matrix_kernel_iff_of_contraction_det_ne_zero (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (hdet : (contractionMatrix p d W hp hW k).det ≠ 0)
    (v : CanonicalIndex d (Macaulay.level d) W (k + 1) → K) :
    Matrix.vecMul v (canonicalMatrix p d (Macaulay.level d) W hp hW k) = 0 ↔
      ∃ w : CanonicalIndex d (Macaulay.level d) W (k + 2) → K,
        Matrix.vecMul w (canonicalMatrix p d (Macaulay.level d) W hp hW (k + 1)) = v := by
  let D := canonicalMatrix p d (Macaulay.level d) W hp hW k
  let B := canonicalMatrix p d (Macaulay.level d) W hp hW (k + 1)
  let H := homotopyMatrix (R := K) d W hW (k + 1)
  let J := homotopyMatrix (R := K) d W hW k
  have hBD : B * D = 0 := canonicalMatrix_mul p d (Macaulay.level d) W hp hW k
  have hA : IsUnit (H * B + D * J).det := isUnit_iff_ne_zero.mpr hdet
  exact MatrixHomotopyExact.vecMul_eq_zero_iff D B H J hBD hA v

theorem weighted_exact_of_contraction_det_ne_zero (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (hdet : (contractionMatrix p d W hp hW k).det ≠ 0) :
    LinearMap.ker (differential p d (Macaulay.level d) W hp hW k) =
      LinearMap.range (differential p d (Macaulay.level d) W hp hW (k + 1)) :=
  FiniteComplexTransport.exact_of_coordinates _ _
    (canonicalMatrix p d (Macaulay.level d) W hp hW k).vecMulLinear
    (canonicalMatrix p d (Macaulay.level d) W hp hW (k + 1)).vecMulLinear
    (canonicalBasis d (Macaulay.level d) W k).equivFun
    (canonicalBasis d (Macaulay.level d) W (k + 1)).equivFun
    (canonicalBasis d (Macaulay.level d) W (k + 2)).equivFun
    (canonicalMatrix_vecMul_coordinates p d (Macaulay.level d) W hp hW k)
    (canonicalMatrix_vecMul_coordinates p d (Macaulay.level d) W hp hW (k + 1))
    (matrix_kernel_iff_of_contraction_det_ne_zero p d W hp hW k hdet)

end Field

variable [IsDomain R]

theorem genericShift_matrix_kernel_iff (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (v : CanonicalIndex d (Macaulay.level d) W (k + 1) → RatFunc R) :
    Matrix.vecMul v (canonicalMatrix (Macaulay.genericShift p d) d (Macaulay.level d) W
      (Macaulay.genericShift_homogeneous p d hp) hW k) = 0 ↔
      ∃ w : CanonicalIndex d (Macaulay.level d) W (k + 2) → RatFunc R,
        Matrix.vecMul w (canonicalMatrix (Macaulay.genericShift p d) d (Macaulay.level d) W
          (Macaulay.genericShift_homogeneous p d hp) hW (k + 1)) = v :=
  matrix_kernel_iff_of_contraction_det_ne_zero _ d W _ hW k
    (contractionMatrix_genericShift_det_ne_zero p d W hp hW k) v

theorem genericShift_weighted_exact (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    LinearMap.ker (differential (Macaulay.genericShift p d) d (Macaulay.level d) W
        (Macaulay.genericShift_homogeneous p d hp) hW k) =
      LinearMap.range (differential (Macaulay.genericShift p d) d (Macaulay.level d) W
        (Macaulay.genericShift_homogeneous p d hp) hW (k + 1)) :=
  weighted_exact_of_contraction_det_ne_zero _ d W _ hW k
    (contractionMatrix_genericShift_det_ne_zero p d W hp hW k)

end LeanCanny.Algebra.KoszulWeighted
