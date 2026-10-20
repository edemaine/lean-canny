/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulGenericContraction
public import LeanCanny.Algebra.MatrixHomotopyExact
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

variable [IsDomain R]

theorem genericShift_matrix_kernel_iff (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (v : CanonicalIndex d (Macaulay.level d) W (k + 1) → RatFunc R) :
    Matrix.vecMul v (canonicalMatrix (Macaulay.genericShift p d) d (Macaulay.level d) W
      (Macaulay.genericShift_homogeneous p d hp) hW k) = 0 ↔
      ∃ w : CanonicalIndex d (Macaulay.level d) W (k + 2) → RatFunc R,
        Matrix.vecMul w (canonicalMatrix (Macaulay.genericShift p d) d (Macaulay.level d) W
          (Macaulay.genericShift_homogeneous p d hp) hW (k + 1)) = v := by
  let D := canonicalMatrix (Macaulay.genericShift p d) d (Macaulay.level d) W
    (Macaulay.genericShift_homogeneous p d hp) hW k
  let B := canonicalMatrix (Macaulay.genericShift p d) d (Macaulay.level d) W
    (Macaulay.genericShift_homogeneous p d hp) hW (k + 1)
  let H := homotopyMatrix (R := RatFunc R) d W hW (k + 1)
  let J := homotopyMatrix (R := RatFunc R) d W hW k
  have hBD : B * D = 0 := canonicalMatrix_mul (Macaulay.genericShift p d) d (Macaulay.level d) W
    (Macaulay.genericShift_homogeneous p d hp) hW k
  have hA : IsUnit (H * B + D * J).det :=
    isUnit_iff_ne_zero.mpr (contractionMatrix_genericShift_det_ne_zero p d W hp hW k)
  exact MatrixHomotopyExact.vecMul_eq_zero_iff D B H J hBD hA v

theorem genericShift_weighted_exact (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    LinearMap.ker (differential (Macaulay.genericShift p d) d (Macaulay.level d) W
        (Macaulay.genericShift_homogeneous p d hp) hW k) =
      LinearMap.range (differential (Macaulay.genericShift p d) d (Macaulay.level d) W
        (Macaulay.genericShift_homogeneous p d hp) hW (k + 1)) := by
  ext x
  constructor
  · intro hx
    have hz : differential (Macaulay.genericShift p d) d (Macaulay.level d) W
        (Macaulay.genericShift_homogeneous p d hp) hW k x = 0 := hx
    have hv : Matrix.vecMul ((canonicalBasis d (Macaulay.level d) W (k + 1)).equivFun x)
        (canonicalMatrix (Macaulay.genericShift p d) d (Macaulay.level d) W
          (Macaulay.genericShift_homogeneous p d hp) hW k) = 0 := by
      rw [canonicalMatrix_vecMul_coordinates, hz, map_zero]
    obtain ⟨w, hw⟩ := (genericShift_matrix_kernel_iff p d W hp hW k _).mp hv
    let y := (canonicalBasis (R := RatFunc R) d (Macaulay.level d) W (k + 2)).equivFun.symm w
    refine ⟨y, ?_⟩
    apply (canonicalBasis (R := RatFunc R) d (Macaulay.level d) W (k + 1)).equivFun.injective
    have hm := canonicalMatrix_vecMul_coordinates (Macaulay.genericShift p d) d (Macaulay.level d) W
      (Macaulay.genericShift_homogeneous p d hp) hW (k + 1) y
    have hy : (canonicalBasis (R := RatFunc R) d (Macaulay.level d) W (k + 2)).equivFun y = w :=
      LinearEquiv.apply_symm_apply _ _
    rw [hy, hw] at hm
    exact hm.symm
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact KoszulExterior.differential_square_zero _ _

end LeanCanny.Algebra.KoszulWeighted
