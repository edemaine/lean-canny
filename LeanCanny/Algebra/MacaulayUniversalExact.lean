/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayUniversalSystem
public import LeanCanny.Algebra.KoszulSpecializationExact
public import LeanCanny.Algebra.KoszulPivotContraction
public import LeanCanny.Algebra.MacaulayEligibilityLevels

/-! # Exactness of the universal finite weighted Koszul complex

For every simultaneous input/spatial ordering, the universal system
specializes to the coordinate powers. Its finite homotopy determinants
therefore specialize to one. Over the universal coefficient fraction field,
the actual weighted differential maps are exact in all positive degrees
and surjective in degree zero.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem contraction_det_specialization (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) (k : ℕ) :
    MvPolynomial.eval (powerPoint (R := R) d)
      (KoszulWeighted.contractionMatrix (system d W π) (d ∘ π) W
        (system_homogeneous d W π) hW k).det = 1 :=
  KoszulWeighted.contractionMatrix_det_specialization (MvPolynomial.eval (powerPoint d))
    (system d W π) (d ∘ π) W (system_homogeneous d W π) hW
    (system_power_specialization d W hdegree π) k

theorem zero_contraction_det_specialization (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) :
    MvPolynomial.eval (powerPoint (R := R) d)
      (KoszulWeighted.zeroContractionMatrix (system d W π) (d ∘ π) W
        (system_homogeneous d W π) hW).det = 1 :=
  KoszulWeighted.zeroContractionMatrix_det_specialization (MvPolynomial.eval (powerPoint d))
    (system d W π) (d ∘ π) W (system_homogeneous d W π) hW
    (system_power_specialization d W hdegree π)

theorem eligibility_det_specialization (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n)) (h : ℕ) :
    MvPolynomial.eval (powerPoint (R := R) d)
      (Macaulay.eligibilityMinor (system d W π) (d ∘ π) W h).det = 1 :=
  Macaulay.eligibilityMinor_det_power_specialization (MvPolynomial.eval (powerPoint d))
    (system d W π) (d ∘ π) W h (system_power_specialization d W hdegree π)

theorem eligibility_det_ne_zero [Nontrivial R] (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n)) (h : ℕ) :
    (Macaulay.eligibilityMinor (system (R := R) d W π) (d ∘ π) W h).det ≠ 0 :=
  Macaulay.eligibilityMinor_det_ne_zero_of_power_specialization (MvPolynomial.eval (powerPoint d))
    (system d W π) (d ∘ π) W h (system_power_specialization d W hdegree π)

noncomputable def fractionSystem (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    MvPolynomial (Fin n) (FractionRing (CoefficientRing n R)) :=
  (system (R := R) d W π i).map (algebraMap (CoefficientRing n R) (FractionRing (CoefficientRing n R)))

theorem fractionSystem_homogeneous (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (fractionSystem (R := R) d W π i).IsHomogeneous (d (π i)) :=
  (system_homogeneous d W π i).map _

noncomputable def fractionDifferential (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) (k : ℕ) :=
  KoszulWeighted.differential (fractionSystem (R := R) d W π) (d ∘ π) (Macaulay.level (d ∘ π)) W
    (fractionSystem_homogeneous d W π) hW k

variable [IsDomain R]

theorem fraction_contraction_det_ne_zero (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) (k : ℕ) :
    (KoszulWeighted.contractionMatrix (fractionSystem (R := R) d W π) (d ∘ π) W
      (fractionSystem_homogeneous d W π) hW k).det ≠ 0 :=
  KoszulWeighted.fraction_contraction_det_ne_zero_of_power_specialization
    (MvPolynomial.eval (powerPoint d)) (system d W π) (d ∘ π) W (system_homogeneous d W π) hW
    (system_power_specialization d W hdegree π) k

theorem fraction_exact (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) (k : ℕ) :
    LinearMap.ker (fractionDifferential (R := R) d W π hW k) =
      LinearMap.range (fractionDifferential (R := R) d W π hW (k + 1)) :=
  KoszulWeighted.fraction_weighted_exact_of_power_specialization
    (MvPolynomial.eval (powerPoint d)) (system d W π) (d ∘ π) W (system_homogeneous d W π) hW
    (system_power_specialization d W hdegree π) k

theorem fraction_zero_surjective (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) :
    Function.Surjective (fractionDifferential (R := R) d W π hW 0) :=
  KoszulWeighted.fraction_weighted_zero_surjective_of_power_specialization
    (MvPolynomial.eval (powerPoint d)) (system d W π) (d ∘ π) W (system_homogeneous d W π) hW
    (system_power_specialization d W hdegree π)

theorem fraction_matrix_kernel_iff (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) (k : ℕ)
    (v : KoszulWeighted.CanonicalIndex (d ∘ π) (Macaulay.level (d ∘ π)) W (k + 1) →
      FractionRing (CoefficientRing n R)) :
    Matrix.vecMul v (KoszulWeighted.canonicalMatrix (fractionSystem d W π) (d ∘ π)
      (Macaulay.level (d ∘ π)) W (fractionSystem_homogeneous d W π) hW k) = 0 ↔
      ∃ w : KoszulWeighted.CanonicalIndex (d ∘ π) (Macaulay.level (d ∘ π)) W (k + 2) →
        FractionRing (CoefficientRing n R),
        Matrix.vecMul w (KoszulWeighted.canonicalMatrix (fractionSystem d W π) (d ∘ π)
          (Macaulay.level (d ∘ π)) W (fractionSystem_homogeneous d W π) hW (k + 1)) = v :=
  KoszulWeighted.matrix_kernel_iff_of_contraction_det_ne_zero
    (fractionSystem (R := R) d W π) (d ∘ π) W (fractionSystem_homogeneous d W π) hW k
    (fraction_contraction_det_ne_zero (R := R) d W hdegree π hW k) v

theorem fraction_pivot_blocks_det_ne_zero (d : Fin n → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) (k : ℕ) :
    (KoszulWeighted.pivotContractionBlock (fractionSystem (R := R) d W π) (d ∘ π) W
      (fractionSystem_homogeneous d W π) hW k).det ≠ 0 ∧
    (KoszulWeighted.nonpivotContractionBlock (fractionSystem (R := R) d W π) (d ∘ π) W
      (fractionSystem_homogeneous d W π) hW k).det ≠ 0 :=
  KoszulWeighted.pivot_blocks_det_ne_zero (fractionSystem (R := R) d W π) (d ∘ π) W
    (fractionSystem_homogeneous d W π) hW k (fraction_contraction_det_ne_zero d W hdegree π hW k)

end LeanCanny.Algebra.MacaulayUniversal
