/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayUniversalExact
public import LeanCanny.Algebra.MacaulayUniversalDenominators
public import LeanCanny.Algebra.KoszulPowerComparisonSpecialization
public import LeanCanny.Algebra.KoszulComparisonRatio

/-! # Universal chain comparisons and their concrete Macaulay ratios

The universal power comparison is invertible in every degree over the
coefficient fraction field. Its alternating determinant quotient is the
actual numerator/extraneous ratio for that ordering. Equality of these
constructed quotients is equivalent to the polynomial cross-comparison
needed for denominator cancellation. Equality across orderings is proved
in `MacaulayUniversalOrdering` using concrete coordinate permutations.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

theorem fraction_powerComparison_det_ne_zero (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) (k : ℕ) :
    (KoszulWeighted.powerComparisonMatrix (fractionSystem (R := R) d W π) (d ∘ π) W
      (fractionSystem_homogeneous (R := R) d W π) hW k).det ≠ 0 :=
  KoszulWeighted.fraction_powerComparison_det_ne_zero (MvPolynomial.eval (powerPoint d))
    (system (R := R) d W π) (d ∘ π) W (system_homogeneous d W π) hW
    (system_power_specialization d W hdegree π) k

noncomputable def fractionComparisonEquiv (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) (k : ℕ) :
    KoszulWeighted.space (R := FractionRing (CoefficientRing n R)) (d ∘ π) (Macaulay.level (d ∘ π)) W k ≃ₗ[
      FractionRing (CoefficientRing n R)]
        KoszulWeighted.space (R := FractionRing (CoefficientRing n R)) (d ∘ π) (Macaulay.level (d ∘ π)) W k :=
  KoszulWeighted.powerComparisonEquiv (fractionSystem (R := R) d W π) (d ∘ π) W
    (fractionSystem_homogeneous (R := R) d W π) hW k (fraction_powerComparison_det_ne_zero (R := R) d W hdegree π hW k)

theorem fractionComparisonEquiv_toLinearMap (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) (k : ℕ) :
    (fractionComparisonEquiv (R := R) d W hdegree π hW k).toLinearMap =
      KoszulWeighted.powerComparison (fractionSystem (R := R) d W π) (d ∘ π) W
        (fractionSystem_homogeneous (R := R) d W π) hW k :=
  KoszulWeighted.powerComparisonEquiv_toLinearMap _ _ _ _ _ _ _

theorem fractionComparisonEquiv_chain (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) (k : ℕ) :
    (fractionDifferential (R := R) d W π hW k).comp
        (fractionComparisonEquiv (R := R) d W hdegree π hW (k + 1)).toLinearMap =
      (fractionComparisonEquiv (R := R) d W hdegree π hW k).toLinearMap.comp
        (KoszulWeighted.differential (Macaulay.powers (R := FractionRing (CoefficientRing n R)) (d ∘ π))
          (d ∘ π) (Macaulay.level (d ∘ π)) W
            (KoszulWeighted.powers_homogeneous (R := FractionRing (CoefficientRing n R)) (d ∘ π)) hW k) := by
  rw [fractionComparisonEquiv_toLinearMap, fractionComparisonEquiv_toLinearMap]
  exact KoszulWeighted.powerComparison_chain (fractionSystem (R := R) d W π) (d ∘ π) W
    (fractionSystem_homogeneous (R := R) d W π) hW k

theorem fraction_comparisonRatio_eq (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n)) (hW : Macaulay.level (d ∘ π) < 2 ^ W) :
    KoszulWeighted.comparisonRatio (fractionSystem (R := R) d W π) (d ∘ π) W
      (fractionSystem_homogeneous (R := R) d W π) hW =
        algebraMap (CoefficientRing n R) (FractionRing (CoefficientRing n R)) (numerator d W π) /
          algebraMap (CoefficientRing n R) (FractionRing (CoefficientRing n R)) (denominator d W π) := by
  rw [KoszulWeighted.comparisonRatio_eq_macaulay (fractionSystem (R := R) d W π) (d ∘ π) W
    (fractionSystem_homogeneous (R := R) d W π) hW
    (fun k => fraction_powerComparison_det_ne_zero (R := R) d W hdegree π hW (k.val + 1))]
  change (Macaulay.activeMinor (fun i => (system (R := R) d W π i).map
      (algebraMap (CoefficientRing n R) (FractionRing (CoefficientRing n R)))) (d ∘ π) W).det /
    (Macaulay.extraneousMinor (fun i => (system (R := R) d W π i).map
      (algebraMap (CoefficientRing n R) (FractionRing (CoefficientRing n R)))) (d ∘ π) W).det = _
  rw [← Macaulay.det_activeMinor_map, ← Macaulay.det_extraneousMinor_map]
  rfl

theorem denominator_ne_zero (d : Fin n → ℕ) (W : ℕ) (hdegree : ∀ i, d i < 2 ^ W)
    (π : Equiv.Perm (Fin n)) : denominator (R := R) d W π ≠ 0 := by
  simpa only [Macaulay.eligibilityMinor_det_two, denominator] using eligibility_det_ne_zero (R := R) d W hdegree π 2

theorem comparisonRatio_eq_iff_cross (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π σ : Equiv.Perm (Fin n))
    (hπ : Macaulay.level (d ∘ π) < 2 ^ W) (hσ : Macaulay.level (d ∘ σ) < 2 ^ W) :
    (KoszulWeighted.comparisonRatio (fractionSystem (R := R) d W π) (d ∘ π) W
        (fractionSystem_homogeneous (R := R) d W π) hπ =
      KoszulWeighted.comparisonRatio (fractionSystem (R := R) d W σ) (d ∘ σ) W
        (fractionSystem_homogeneous (R := R) d W σ) hσ) ↔
      numerator (R := R) d W π * denominator d W σ = numerator d W σ * denominator d W π := by
  have hd (τ : Equiv.Perm (Fin n)) :
      algebraMap (CoefficientRing n R) (FractionRing (CoefficientRing n R)) (denominator d W τ) ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact denominator_ne_zero d W hdegree τ
  rw [fraction_comparisonRatio_eq d W hdegree π hπ, fraction_comparisonRatio_eq d W hdegree σ hσ,
    div_eq_div_iff (hd π) (hd σ), ← map_mul, ← map_mul]
  exact (IsFractionRing.injective (CoefficientRing n R) (FractionRing (CoefficientRing n R))).eq_iff

end LeanCanny.Algebra.MacaulayUniversal
