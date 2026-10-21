/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicRegularPersistence
public import LeanCanny.ETR.TubeDeformationSpecialization

/-! # Effective nonvanishing of the lowest tube quotient coefficient

The lowest numerator coefficient is the product of the lowest quotient and
extraneous coefficients. Nonvanishing of the padded deformation coefficient
therefore forces nonvanishing of the quotient coefficient after specialization.
The existing effective dyadic interval supplies a nonzero projection polynomial
covering all affine roots with invertible Jacobian.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Encoding LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

theorem polynomial_trailingCoeff_map_ne_zero_of_deformation_lowest {S : Type*} [CommRing S]
    (φ : Polynomial (Polynomial ℤ) →+* S)
    (hfull : φ (TubeDeformation.lowestCoefficient source active n d ell c) ≠ 0) :
    φ (polynomial source active n d ell c).trailingCoeff ≠ 0 := by
  have hchar : φ (TubeDeformation.characteristicPolynomial source active n d ell c).trailingCoeff ≠ 0 := by
    intro hz
    exact hfull ((TubeDeformation.characteristicLowest_eval_zero_iff φ source active n d ell c).mp hz)
  have hn : φ (numerator source active n d ell c).trailingCoeff ≠ 0 := by
    rw [(numerator_lowest source active n d ell c).2]
    exact hchar
  intro hz
  apply hn
  rw [polynomial_factorization, Polynomial.trailingCoeff_mul, map_mul, hz, zero_mul]

theorem lowestProjectionPolynomial_ne_zero_of_small (read : List Bool → List Bool)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ InfinitesimalSign.dyadic
      (Nat.fromBitsLE (TubeDeformation.specializationExponent source read B.degree B.bits c))) :
    lowestProjectionPolynomial source active n d ell c epsilon ≠ 0 := by
  exact polynomial_trailingCoeff_map_ne_zero_of_deformation_lowest source active n d ell c
    (Polynomial.mapRingHom (Polynomial.eval₂RingHom (Int.castRingHom ℝ) epsilon))
    (TubeDeformation.projectionPolynomial_ne_zero_of_small source active read n d ell B hr c epsilon hepsilon hsmall)

theorem small_specialization_preserves_polynomial_lowest (read : List Bool → List Bool)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ InfinitesimalSign.dyadic
      (Nat.fromBitsLE (TubeDeformation.specializationExponent source read B.degree B.bits c))) :
    let φ := Polynomial.mapRingHom (Polynomial.eval₂RingHom (Int.castRingHom ℝ) epsilon)
    ((polynomial source active n d ell c).map φ).natTrailingDegree =
        (polynomial source active n d ell c).natTrailingDegree ∧
      ((polynomial source active n d ell c).map φ).trailingCoeff =
        lowestProjectionPolynomial source active n d ell c epsilon :=
  DeformationLowestCoefficient.trailingCoeff_map_of_nonzero _ _
    (lowestProjectionPolynomial_ne_zero_of_small source active n d ell c read B hr epsilon hepsilon hsmall)

theorem finite_regular_projection_values_of_small (read : List Bool → List Bool)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ InfinitesimalSign.dyadic
      (Nat.fromBitsLE (TubeDeformation.specializationExponent source read B.degree B.bits c))) :
    {u : ℝ | ∃ y, regularSystem source active n d ell c epsilon (u, y) = 0 ∧
      (fderiv ℝ (regularSystem source active n d ell c epsilon) (u, y)).IsInvertible}.Finite := by
  apply (Polynomial.finite_setOfPred_isRoot
    (lowestProjectionPolynomial_ne_zero_of_small source active n d ell c read B hr epsilon hepsilon hsmall)).subset
  rintro u ⟨y, hy, hJac⟩
  exact lowestProjectionPolynomial_eval_eq_zero_of_regular_root source active n d ell c epsilon (u, y) hy hJac

end LeanCanny.ETR.TubeCharacteristicQuotient
