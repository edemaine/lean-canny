/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulGenericExact
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Exactness from a coordinate-power specialization

If a homogeneous system specializes to the coordinate powers, its finite
homotopy determinants specialize to one. Over a domain they are nonzero,
so the weighted complex is exact over the coefficient fraction field.
This argument applies to the original system without a characteristic shift.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

theorem contractionMatrix_congr {p q : Fin n → Poly n R} (he : p = q)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (hq : ∀ i, (q i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    contractionMatrix p d W hp hW k = contractionMatrix q d W hq hW k := by
  subst q
  rfl

theorem contractionMatrix_power_specialization (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) (k : ℕ) :
    (contractionMatrix p d W hp hW k).map φ = 1 := by
  rw [← contractionMatrix_map φ p d W hp hW k,
    contractionMatrix_congr (funext hpower) d W _ (powers_homogeneous d) hW k]
  exact homotopyMatrix_identity d W hW k

theorem contractionMatrix_det_specialization (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) (k : ℕ) :
    φ (contractionMatrix p d W hp hW k).det = 1 := by
  rw [φ.map_det]
  change ((contractionMatrix p d W hp hW k).map φ).det = 1
  rw [contractionMatrix_power_specialization φ p d W hp hW hpower k, Matrix.det_one]

theorem contractionMatrix_det_ne_zero_of_power_specialization [Nontrivial S] (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) (k : ℕ) :
    (contractionMatrix p d W hp hW k).det ≠ 0 := by
  intro hz
  have h := contractionMatrix_det_specialization φ p d W hp hW hpower k
  rw [hz, map_zero] at h
  exact zero_ne_one h

noncomputable def zeroContractionMatrix (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    Matrix (CanonicalIndex d (Macaulay.level d) W 0) (CanonicalIndex d (Macaulay.level d) W 0) R :=
  homotopyMatrix d W hW 0 * canonicalMatrix p d (Macaulay.level d) W hp hW 0

theorem zeroContractionMatrix_map (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    zeroContractionMatrix (fun i => (p i).map φ) d W (fun i => (hp i).map φ) hW =
      (zeroContractionMatrix p d W hp hW).map φ := by
  unfold zeroContractionMatrix
  rw [homotopyMatrix_map φ, canonicalMatrix_map, Matrix.map_mul]

theorem zeroContractionMatrix_det_specialization (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) :
    φ (zeroContractionMatrix p d W hp hW).det = 1 := by
  rw [φ.map_det]
  change ((zeroContractionMatrix p d W hp hW).map φ).det = 1
  rw [← zeroContractionMatrix_map φ p d W hp hW]
  unfold zeroContractionMatrix
  rw [canonicalMatrix_congr (funext hpower) d (Macaulay.level d) W _ (powers_homogeneous d) hW 0,
    homotopyMatrix_zero_identity, Matrix.det_one]

theorem zeroContractionMatrix_det_ne_zero_of_power_specialization [Nontrivial S] (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) :
    (zeroContractionMatrix p d W hp hW).det ≠ 0 := by
  intro hz
  have h := zeroContractionMatrix_det_specialization φ p d W hp hW hpower
  rw [hz, map_zero] at h
  exact zero_ne_one h

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
      LinearMap.range (differential p d (Macaulay.level d) W hp hW (k + 1)) := by
  ext x
  constructor
  · intro hx
    have hz : differential p d (Macaulay.level d) W hp hW k x = 0 := hx
    have hv : Matrix.vecMul ((canonicalBasis d (Macaulay.level d) W (k + 1)).equivFun x)
        (canonicalMatrix p d (Macaulay.level d) W hp hW k) = 0 := by
      rw [canonicalMatrix_vecMul_coordinates, hz, map_zero]
    obtain ⟨w, hw⟩ := (matrix_kernel_iff_of_contraction_det_ne_zero p d W hp hW k hdet _).mp hv
    let y := (canonicalBasis (R := K) d (Macaulay.level d) W (k + 2)).equivFun.symm w
    refine ⟨y, ?_⟩
    apply (canonicalBasis (R := K) d (Macaulay.level d) W (k + 1)).equivFun.injective
    have hm := canonicalMatrix_vecMul_coordinates p d (Macaulay.level d) W hp hW (k + 1) y
    have hy : (canonicalBasis (R := K) d (Macaulay.level d) W (k + 2)).equivFun y = w :=
      LinearEquiv.apply_symm_apply _ _
    rw [hy, hw] at hm
    exact hm.symm
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact KoszulExterior.differential_square_zero _ _

theorem matrix_zero_surjective_of_contraction_det_ne_zero (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hdet : (zeroContractionMatrix p d W hp hW).det ≠ 0) :
    Function.Surjective (fun v => Matrix.vecMul v (canonicalMatrix p d (Macaulay.level d) W hp hW 0)) := by
  have hu : IsUnit (zeroContractionMatrix p d W hp hW) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  intro v
  obtain ⟨w, hw⟩ := Matrix.vecMul_surjective_iff_isUnit.mpr hu v
  dsimp only at hw
  exact ⟨Matrix.vecMul w (homotopyMatrix d W hW 0), by
    dsimp only
    rw [Matrix.vecMul_vecMul]
    exact hw⟩

theorem weighted_zero_surjective_of_contraction_det_ne_zero (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hdet : (zeroContractionMatrix p d W hp hW).det ≠ 0) :
    Function.Surjective (differential p d (Macaulay.level d) W hp hW 0) := by
  intro x
  obtain ⟨w, hw⟩ := matrix_zero_surjective_of_contraction_det_ne_zero p d W hp hW hdet
    ((canonicalBasis (R := K) d (Macaulay.level d) W 0).equivFun x)
  dsimp only at hw
  let y := (canonicalBasis (R := K) d (Macaulay.level d) W 1).equivFun.symm w
  refine ⟨y, ?_⟩
  apply (canonicalBasis (R := K) d (Macaulay.level d) W 0).equivFun.injective
  have hm := canonicalMatrix_vecMul_coordinates p d (Macaulay.level d) W hp hW 0 y
  have hy : (canonicalBasis (R := K) d (Macaulay.level d) W 1).equivFun y = w :=
    LinearEquiv.apply_symm_apply _ _
  rw [hy, hw] at hm
  exact hm.symm

end Field

section FractionField
variable [Nontrivial S] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem fraction_contraction_det_ne_zero_of_power_specialization (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) (k : ℕ) :
    (contractionMatrix (fun i => (p i).map (algebraMap R K)) d W
      (fun i => (hp i).map (algebraMap R K)) hW k).det ≠ 0 := by
  rw [contractionMatrix_map (algebraMap R K) p d W hp hW k]
  have hm := (algebraMap R K).map_det (contractionMatrix p d W hp hW k)
  change (algebraMap R K) (contractionMatrix p d W hp hW k).det =
    ((contractionMatrix p d W hp hW k).map (algebraMap R K)).det at hm
  rw [← hm, ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact contractionMatrix_det_ne_zero_of_power_specialization φ p d W hp hW hpower k

theorem fraction_zero_contraction_det_ne_zero_of_power_specialization (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) :
    (zeroContractionMatrix (fun i => (p i).map (algebraMap R K)) d W
      (fun i => (hp i).map (algebraMap R K)) hW).det ≠ 0 := by
  rw [zeroContractionMatrix_map (algebraMap R K) p d W hp hW]
  have hm := (algebraMap R K).map_det (zeroContractionMatrix p d W hp hW)
  change (algebraMap R K) (zeroContractionMatrix p d W hp hW).det =
    ((zeroContractionMatrix p d W hp hW).map (algebraMap R K)).det at hm
  rw [← hm, ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact zeroContractionMatrix_det_ne_zero_of_power_specialization φ p d W hp hW hpower

theorem fraction_weighted_exact_of_power_specialization (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) (k : ℕ) :
    LinearMap.ker (differential (fun i => (p i).map (algebraMap R K)) d (Macaulay.level d) W
        (fun i => (hp i).map (algebraMap R K)) hW k) =
      LinearMap.range (differential (fun i => (p i).map (algebraMap R K)) d (Macaulay.level d) W
        (fun i => (hp i).map (algebraMap R K)) hW (k + 1)) :=
  weighted_exact_of_contraction_det_ne_zero _ d W _ hW k
    (fraction_contraction_det_ne_zero_of_power_specialization φ p d W hp hW hpower k)

theorem fraction_weighted_zero_surjective_of_power_specialization (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) :
    Function.Surjective (differential (fun i => (p i).map (algebraMap R K)) d (Macaulay.level d) W
      (fun i => (hp i).map (algebraMap R K)) hW 0) :=
  weighted_zero_surjective_of_contraction_det_ne_zero _ d W _ hW
    (fraction_zero_contraction_det_ne_zero_of_power_specialization φ p d W hp hW hpower)

end FractionField
end LeanCanny.Algebra.KoszulWeighted
