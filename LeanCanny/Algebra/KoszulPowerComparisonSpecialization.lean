/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulPowerComparison

/-! # Specialization and invertibility of the power comparison

The comparison matrices commute with coefficient maps and specialize to
the identity at coordinate powers. Their determinants are therefore
nonzero when such a specialization exists. Over a field this gives an
explicit equivalence in every degree, intertwining the two differentials.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

theorem powerComparisonMatrix_congr {p q : Fin n → Poly n R} (he : p = q)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (hq : ∀ i, (q i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    powerComparisonMatrix p d W hp hW k = powerComparisonMatrix q d W hq hW k := by
  subst q
  rfl

theorem powerComparisonMatrix_map (φ : R →+* S) (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    powerComparisonMatrix (fun i => (p i).map φ) d W (fun i => (hp i).map φ) hW k =
      (powerComparisonMatrix p d W hp hW k).map φ := by
  cases k with
  | zero => rw [powerComparisonMatrix_zero, powerComparisonMatrix_zero, zeroContractionMatrix_map]
  | succ k =>
    rw [powerComparisonMatrix_succ, powerComparisonMatrix_succ, homotopyMatrix_map φ, homotopyMatrix_map φ,
      canonicalMatrix_map φ p d (Macaulay.level d) W hp hW (k + 1), canonicalMatrix_powers_map φ,
      ← Matrix.map_mul, ← Matrix.map_mul]
    funext a b
    exact (φ.map_add _ _).symm

theorem powerComparisonMatrix_specialization (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) (k : ℕ) :
    (powerComparisonMatrix p d W hp hW k).map φ = 1 := by
  rw [← powerComparisonMatrix_map φ p d W hp hW k,
    powerComparisonMatrix_congr (funext hpower) d W _ (powers_homogeneous d) hW k, powerComparisonMatrix_powers]

theorem powerComparisonMatrix_det_specialization (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) (k : ℕ) :
    φ (powerComparisonMatrix p d W hp hW k).det = 1 := by
  rw [φ.map_det]
  change ((powerComparisonMatrix p d W hp hW k).map φ).det = 1
  rw [powerComparisonMatrix_specialization φ p d W hp hW hpower k, Matrix.det_one]

theorem powerComparisonMatrix_det_ne_zero_of_specialization [Nontrivial S] (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) (k : ℕ) :
    (powerComparisonMatrix p d W hp hW k).det ≠ 0 := by
  intro hz
  have he := powerComparisonMatrix_det_specialization φ p d W hp hW hpower k
  rw [hz, map_zero] at he
  exact zero_ne_one he

section Field
variable {K : Type*} [Field K]

theorem powerComparison_bijective (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (hdet : (powerComparisonMatrix p d W hp hW k).det ≠ 0) :
    Function.Bijective (powerComparison p d W hp hW k) := by
  have hd : (powerComparison p d W hp hW k).det ≠ 0 := by
    rw [← LinearMap.det_toMatrix (canonicalBasis (R := K) d (Macaulay.level d) W k), ← Matrix.det_transpose]
    exact hdet
  have hu := (LinearMap.isUnit_iff_isUnit_det (powerComparison p d W hp hW k)).mpr (isUnit_iff_ne_zero.mpr hd)
  have hi := LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp hu)
  exact ⟨hi, LinearMap.surjective_of_injective hi⟩

noncomputable def powerComparisonEquiv (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (hdet : (powerComparisonMatrix p d W hp hW k).det ≠ 0) :
    space (R := K) d (Macaulay.level d) W k ≃ₗ[K] space (R := K) d (Macaulay.level d) W k :=
  LinearEquiv.ofBijective (powerComparison p d W hp hW k) (powerComparison_bijective p d W hp hW k hdet)

theorem powerComparisonEquiv_toLinearMap (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (hdet : (powerComparisonMatrix p d W hp hW k).det ≠ 0) :
    (powerComparisonEquiv p d W hp hW k hdet).toLinearMap = powerComparison p d W hp hW k := rfl

end Field

section FractionField
variable [Nontrivial S] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem fraction_powerComparison_det_ne_zero (φ : R →+* S)
    (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hpower : ∀ i, (p i).map φ = Macaulay.powers (R := S) d i) (k : ℕ) :
    (powerComparisonMatrix (fun i => (p i).map (algebraMap R K)) d W
      (fun i => (hp i).map (algebraMap R K)) hW k).det ≠ 0 := by
  rw [powerComparisonMatrix_map (algebraMap R K) p d W hp hW k]
  have hm := (algebraMap R K).map_det (powerComparisonMatrix p d W hp hW k)
  change (algebraMap R K) (powerComparisonMatrix p d W hp hW k).det =
    ((powerComparisonMatrix p d W hp hW k).map (algebraMap R K)).det at hm
  rw [← hm, ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact powerComparisonMatrix_det_ne_zero_of_specialization φ p d W hp hW hpower k

end FractionField
end LeanCanny.Algebra.KoszulWeighted
