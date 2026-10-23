/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulGenericExact
public import LeanCanny.Algebra.MatrixScalarTransport
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
    φ (contractionMatrix p d W hp hW k).det = 1 :=
  MatrixScalarTransport.det_specialization φ _
    (contractionMatrix_power_specialization φ p d W hp hW hpower k)

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

section Field
variable {K : Type*} [Field K]

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
    Function.Surjective (differential p d (Macaulay.level d) W hp hW 0) :=
  (weighted_surjective_iff_matrix p d (Macaulay.level d) W hp hW 0).mpr
    (matrix_zero_surjective_of_contraction_det_ne_zero p d W hp hW hdet)

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
  exact MatrixScalarTransport.det_map_ne_zero_of_specialization φ (algebraMap R K)
    (IsFractionRing.injective R K) _ (contractionMatrix_det_specialization φ p d W hp hW hpower k)

theorem fraction_zero_contraction_det_ne_zero_of_power_specialization (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) :
    (zeroContractionMatrix (fun i => (p i).map (algebraMap R K)) d W
      (fun i => (hp i).map (algebraMap R K)) hW).det ≠ 0 := by
  rw [zeroContractionMatrix_map (algebraMap R K) p d W hp hW]
  exact MatrixScalarTransport.det_map_ne_zero_of_specialization φ (algebraMap R K)
    (IsFractionRing.injective R K) _ (zeroContractionMatrix_det_specialization φ p d W hp hW hpower)

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
