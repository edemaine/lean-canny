/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayUniversalComparison
public import LeanCanny.Algebra.KoszulComparisonTransport

/-! # Coordinate transport suffices for universal polynomial comparisons

The universal comparison determinants are already nonzero. A simultaneous
transport of the input and coordinate-power finite complexes therefore
proves the actual polynomial numerator/denominator cross-comparison.
`MacaulayUniversalOrdering` constructs this transport for coordinate permutations.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

theorem cross_of_transport (d : Fin n → ℕ) (W : ℕ) (hdegree : ∀ i, d i < 2 ^ W)
    (π σ : Equiv.Perm (Fin n)) (hπ : Macaulay.level (d ∘ π) < 2 ^ W) (hσ : Macaulay.level (d ∘ σ) < 2 ^ W)
    (T : (k : ℕ) →
      KoszulWeighted.space (R := FractionRing (CoefficientRing n R)) (d ∘ π) (Macaulay.level (d ∘ π)) W k ≃ₗ[
        FractionRing (CoefficientRing n R)]
          KoszulWeighted.space (R := FractionRing (CoefficientRing n R)) (d ∘ σ) (Macaulay.level (d ∘ σ)) W k)
    (hpower : ∀ k,
      (KoszulWeighted.differential (Macaulay.powers (R := FractionRing (CoefficientRing n R)) (d ∘ σ))
        (d ∘ σ) (Macaulay.level (d ∘ σ)) W
          (KoszulWeighted.powers_homogeneous (R := FractionRing (CoefficientRing n R)) (d ∘ σ)) hσ k).comp
            (T (k + 1)).toLinearMap =
      (T k).toLinearMap.comp
        (KoszulWeighted.differential (Macaulay.powers (R := FractionRing (CoefficientRing n R)) (d ∘ π))
          (d ∘ π) (Macaulay.level (d ∘ π)) W
            (KoszulWeighted.powers_homogeneous (R := FractionRing (CoefficientRing n R)) (d ∘ π)) hπ k))
    (hinput : ∀ k, (fractionDifferential (R := R) d W σ hσ k).comp (T (k + 1)).toLinearMap =
      (T k).toLinearMap.comp (fractionDifferential (R := R) d W π hπ k)) :
    numerator (R := R) d W π * denominator d W σ = numerator d W σ * denominator d W π := by
  apply (comparisonRatio_eq_iff_cross (R := R) d W hdegree π σ hπ hσ).mp
  exact KoszulWeighted.comparisonRatio_eq_of_transport (fractionSystem (R := R) d W π)
    (fractionSystem (R := R) d W σ) (d ∘ π) (d ∘ σ) W W
    (fractionSystem_homogeneous (R := R) d W π) (fractionSystem_homogeneous (R := R) d W σ) hπ hσ
    (fraction_powerComparison_det_ne_zero (R := R) d W hdegree π hπ)
    (fraction_powerComparison_det_ne_zero (R := R) d W hdegree σ hσ) T hpower hinput

end LeanCanny.Algebra.MacaulayUniversal
