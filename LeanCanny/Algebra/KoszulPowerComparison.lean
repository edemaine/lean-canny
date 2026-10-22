/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayPivotBoundary

/-! # A chain comparison from coordinate powers to a homogeneous system

The operator `F = D H + H D₀` intertwines the coordinate-power differential
`D₀` with the input differential `D`. It is the identity at coordinate
powers and on the incoming homotopy summand. Its positive-degree determinant
is the existing nonpivot contraction determinant; its degree-zero
determinant is the active Macaulay numerator.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def powerComparison (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (k : ℕ) → Module.End R (space (R := R) d (Macaulay.level d) W k)
  | 0 => (differential p d (Macaulay.level d) W hp hW 0).comp (weightedHomotopy d W hW 0)
  | k + 1 => (differential p d (Macaulay.level d) W hp hW (k + 1)).comp (weightedHomotopy d W hW (k + 1)) +
      (weightedHomotopy d W hW k).comp
        (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k)

theorem powerComparison_chain (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (differential p d (Macaulay.level d) W hp hW k).comp (powerComparison p d W hp hW (k + 1)) =
      (powerComparison p d W hp hW k).comp
        (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k) := by
  cases k with
  | zero =>
    apply LinearMap.ext
    intro x
    have hd := LinearMap.congr_fun (differential_comp p d (Macaulay.level d) W hp hW 0)
      (weightedHomotopy d W hW 1 x)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hd
    change differential p d (Macaulay.level d) W hp hW 0
      (differential p d (Macaulay.level d) W hp hW 1 (weightedHomotopy d W hW 1 x) +
        weightedHomotopy d W hW 0 (differential (Macaulay.powers d) d (Macaulay.level d) W (powers_homogeneous d) hW 0 x)) = _
    rw [map_add, hd, zero_add]
    rfl
  | succ k =>
    apply LinearMap.ext
    intro x
    have hd := LinearMap.congr_fun (differential_comp p d (Macaulay.level d) W hp hW (k + 1))
      (weightedHomotopy d W hW (k + 1 + 1) x)
    have he := LinearMap.congr_fun (differential_comp (Macaulay.powers (R := R) d) d (Macaulay.level d) W
      (powers_homogeneous d) hW k) x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hd he
    change differential p d (Macaulay.level d) W hp hW (k + 1)
      (differential p d (Macaulay.level d) W hp hW (k + 1 + 1) (weightedHomotopy d W hW (k + 1 + 1) x) +
        weightedHomotopy d W hW (k + 1)
          (differential (Macaulay.powers d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1) x)) =
      differential p d (Macaulay.level d) W hp hW (k + 1)
        (weightedHomotopy d W hW (k + 1)
          (differential (Macaulay.powers d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1) x)) +
      weightedHomotopy d W hW k
        (differential (Macaulay.powers d) d (Macaulay.level d) W (powers_homogeneous d) hW k
          (differential (Macaulay.powers d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1) x))
    rw [map_add, hd, zero_add, he, map_zero, add_zero]

theorem powerComparison_powers (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    powerComparison (Macaulay.powers (R := R) d) d W (powers_homogeneous d) hW k = LinearMap.id := by
  cases k with
  | zero => exact weightedHomotopy_zero_identity d W hW
  | succ k => exact weightedHomotopy_identity d W hW k

theorem powerComparison_on_pivot (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (x : space (R := R) d (Macaulay.level d) W (k + 1)) (hx : x ∈ pivotSpan (R := R) d W (k + 1)) :
    powerComparison p d W hp hW (k + 1) x = x := by
  have hz := pivotSpan_le_homotopy_kernel d W hW (k + 1) hx
  change weightedHomotopy d W hW (k + 1) x = 0 at hz
  have hi := LinearMap.congr_fun (weightedHomotopy_identity (R := R) d W hW k) x
  change differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1)
      (weightedHomotopy d W hW (k + 1) x) +
    weightedHomotopy d W hW k
      (differential (Macaulay.powers d) d (Macaulay.level d) W (powers_homogeneous d) hW k x) = x at hi
  rw [hz, map_zero, zero_add] at hi
  change differential p d (Macaulay.level d) W hp hW (k + 1) (weightedHomotopy d W hW (k + 1) x) + _ = x
  rw [hz, map_zero, zero_add]
  exact hi

noncomputable def powerComparisonMatrix (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :=
  (LinearMap.toMatrix (canonicalBasis d (Macaulay.level d) W k) (canonicalBasis d (Macaulay.level d) W k)
    (powerComparison p d W hp hW k))ᵀ

theorem powerComparisonMatrix_zero (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    powerComparisonMatrix p d W hp hW 0 = zeroContractionMatrix p d W hp hW :=
  zeroOperator_matrix p d W hp hW

theorem powerComparisonMatrix_det_zero (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (powerComparisonMatrix p d W hp hW 0).det = (Macaulay.activeMinor p d W).det := by
  rw [powerComparisonMatrix_zero, zeroContractionMatrix_det_active]

theorem powerComparisonMatrix_succ (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    powerComparisonMatrix p d W hp hW (k + 1) =
      homotopyMatrix d W hW (k + 1) * canonicalMatrix p d (Macaulay.level d) W hp hW (k + 1) +
        canonicalMatrix (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k *
          homotopyMatrix d W hW k := by
  unfold powerComparisonMatrix powerComparison homotopyMatrix canonicalMatrix
  rw [map_add,
    LinearMap.toMatrix_comp (canonicalBasis d (Macaulay.level d) W (k + 1))
      (canonicalBasis d (Macaulay.level d) W (k + 2)) (canonicalBasis d (Macaulay.level d) W (k + 1)),
    LinearMap.toMatrix_comp (canonicalBasis d (Macaulay.level d) W (k + 1))
      (canonicalBasis d (Macaulay.level d) W k) (canonicalBasis d (Macaulay.level d) W (k + 1)),
    Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul]

theorem powerComparisonMatrix_powers (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    powerComparisonMatrix (Macaulay.powers (R := R) d) d W (powers_homogeneous d) hW k = 1 := by
  rw [powerComparisonMatrix, powerComparison_powers, LinearMap.toMatrix_id, Matrix.transpose_one]

theorem powerComparisonMatrix_chain (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    powerComparisonMatrix p d W hp hW (k + 1) * canonicalMatrix p d (Macaulay.level d) W hp hW k =
      canonicalMatrix (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k *
        powerComparisonMatrix p d W hp hW k := by
  unfold powerComparisonMatrix canonicalMatrix
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← LinearMap.toMatrix_comp,
    ← LinearMap.toMatrix_comp, powerComparison_chain]

theorem powerComparisonMatrix_pivot_row (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (a b : CanonicalIndex d (Macaulay.level d) W (k + 1)) (ha : HasPivot d W (k + 1) a) :
    powerComparisonMatrix p d W hp hW (k + 1) a b = (1 : Matrix _ _ R) a b := by
  rw [powerComparisonMatrix, Matrix.transpose_apply, LinearMap.toMatrix_apply,
    powerComparison_on_pivot p d W hp hW k _ (Submodule.subset_span ⟨a, ha, rfl⟩), Module.Basis.repr_self_apply]
  rfl

theorem pivotSpan_coordinate_zero (d : Fin n → ℕ) (W k : ℕ)
    (x : space (R := R) d (Macaulay.level d) W k) (hx : x ∈ pivotSpan (R := R) d W k)
    (b : CanonicalIndex d (Macaulay.level d) W k) (hb : ¬HasPivot d W k b) :
    (canonicalBasis (R := R) d (Macaulay.level d) W k).repr x b = 0 := by
  have hs := (canonicalBasis (R := R) d (Macaulay.level d) W k).mem_span_image.mp hx
  by_contra hn
  exact hb (hs (Finsupp.mem_support_iff.mpr hn))

theorem powerComparisonMatrix_nonpivot_column (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (a b : CanonicalIndex d (Macaulay.level d) W (k + 1)) (hb : ¬HasPivot d W (k + 1) b) :
    powerComparisonMatrix p d W hp hW (k + 1) a b = contractionMatrix p d W hp hW k a b := by
  have hz (y : space (R := R) d (Macaulay.level d) W k) :
      (canonicalBasis (R := R) d (Macaulay.level d) W (k + 1)).repr (weightedHomotopy d W hW k y) b = 0 :=
    pivotSpan_coordinate_zero d W (k + 1) _
      (by rw [← homotopy_range_eq_pivotSpan (R := R) d W hW k]; exact ⟨y, rfl⟩) b hb
  rw [powerComparisonMatrix, ← homotopyOperator_matrix p d W hp hW k,
    Matrix.transpose_apply, Matrix.transpose_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simp only [powerComparison, homotopyOperator, LinearMap.add_apply, LinearMap.comp_apply,
    map_add, Finsupp.add_apply, hz, add_zero]

theorem powerComparisonMatrix_det_succ (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (powerComparisonMatrix p d W hp hW (k + 1)).det = (nonpivotContractionBlock p d W hp hW k).det := by
  have htri : ∀ a, HasPivot d W (k + 1) a → ∀ b, ¬HasPivot d W (k + 1) b →
      powerComparisonMatrix p d W hp hW (k + 1) a b = 0 := by
    intro a ha b hb
    rw [powerComparisonMatrix_pivot_row p d W hp hW k a b ha]
    exact Matrix.one_apply_ne (fun he => hb (he ▸ ha))
  rw [Matrix.twoBlockTriangular_det' _ _ htri]
  have hfirst : Matrix.toSquareBlockProp (powerComparisonMatrix p d W hp hW (k + 1))
      (HasPivot d W (k + 1)) = 1 := by
    ext a b
    change powerComparisonMatrix p d W hp hW (k + 1) a.val b.val = _
    rw [powerComparisonMatrix_pivot_row p d W hp hW k a.val b.val a.property]
    simp only [Matrix.one_apply, Subtype.val_injective.eq_iff]
  have hsecond : Matrix.toSquareBlockProp (powerComparisonMatrix p d W hp hW (k + 1))
      (fun a => ¬HasPivot d W (k + 1) a) = nonpivotContractionBlock p d W hp hW k := by
    ext a b
    exact powerComparisonMatrix_nonpivot_column p d W hp hW k a.val b.val b.property
  rw [hfirst, hsecond, Matrix.det_one, one_mul]

end LeanCanny.Algebra.KoszulWeighted
