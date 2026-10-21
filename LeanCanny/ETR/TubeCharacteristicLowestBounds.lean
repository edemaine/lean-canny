/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicLowestSpecialization
public import LeanCanny.Algebra.CharacteristicCoefficientDegree

/-! # Degree and root-count bounds for the lowest tube projection polynomial

The full characteristic numerator has projection-parameter degree at most
the padded matrix dimension in every characteristic coefficient. The lowest
quotient coefficient divides the lowest numerator coefficient, giving the
same bound after perturbation specialization. In the effective nonvanishing
interval, at most that many distinct projection values occur at affine
solutions with invertible Jacobian. Singular solutions remain outside this
regular-point result.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open scoped Classical BigOperators
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det
variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

theorem characteristicLowest_projection_degree_le :
    (TubeDeformation.characteristicPolynomial source active n d ell c).trailingCoeff.natDegree ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) := by
  have hA (r s) : (TubeBivariate.integerMatrix source active n d ell c r s).natDegree ≤ 1 :=
    Macaulay.polynomial_entry_degree_le _ _ _ 1 (TubeDeformation.original_row_outer_degree source active n d ell c) r s
  have he := AffineCharacteristic.subtractive_det_coefficient_degree
    (TubeBivariate.integerMatrix source active n d ell c) 1 hA
    (TubeDeformation.characteristicPolynomial source active n d ell c).natTrailingDegree
  simpa only [Fintype.card_fin, mul_one, Polynomial.trailingCoeff, TubeDeformation.characteristicPolynomial,
    Macaulay.characteristicNumerator, TubeBivariate.integerMatrix] using he

theorem polynomial_trailingCoeff_dvd_characteristicLowest :
    (polynomial source active n d ell c).trailingCoeff ∣
      (TubeDeformation.characteristicPolynomial source active n d ell c).trailingCoeff := by
  refine ⟨(TubeExtraneous.characteristicPolynomial source active n d ell c).trailingCoeff, ?_⟩
  rw [← (numerator_lowest source active n d ell c).2, polynomial_factorization, Polynomial.trailingCoeff_mul]

theorem polynomial_trailingCoeff_projection_degree_le :
    (polynomial source active n d ell c).trailingCoeff.natDegree ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) :=
  (Polynomial.natDegree_le_of_dvd (polynomial_trailingCoeff_dvd_characteristicLowest source active n d ell c)
    (TubeDeformation.characteristicLowest_ne_zero source active n d ell c)).trans
    (characteristicLowest_projection_degree_le source active n d ell c)

theorem lowestProjectionPolynomial_natDegree_le {K : Type*} [RCLike K] (epsilon : K) :
    (lowestProjectionPolynomial source active n d ell c epsilon).natDegree ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) :=
  Polynomial.natDegree_map_le.trans (polynomial_trailingCoeff_projection_degree_le source active n d ell c)

theorem lowestProjectionPolynomial_roots_card_le {K : Type*} [RCLike K] (epsilon : K) :
    (lowestProjectionPolynomial source active n d ell c epsilon).roots.card ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) :=
  (Polynomial.card_roots' _).trans (lowestProjectionPolynomial_natDegree_le source active n d ell c epsilon)

theorem regular_projection_values_ncard_le_of_small (read : List Bool → List Bool)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ InfinitesimalSign.dyadic
      (Nat.fromBitsLE (TubeDeformation.specializationExponent source read B.degree B.bits c))) :
    {u : ℝ | ∃ y, regularSystem source active n d ell c epsilon (u, y) = 0 ∧
      (fderiv ℝ (regularSystem source active n d ell c epsilon) (u, y)).IsInvertible}.ncard ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) := by
  let p := lowestProjectionPolynomial source active n d ell c epsilon
  have hp : p ≠ 0 := lowestProjectionPolynomial_ne_zero_of_small source active n d ell c read B hr epsilon hepsilon hsmall
  have hsub : {u : ℝ | ∃ y, regularSystem source active n d ell c epsilon (u, y) = 0 ∧
      (fderiv ℝ (regularSystem source active n d ell c epsilon) (u, y)).IsInvertible} ⊆ (p.roots.toFinset : Set ℝ) := by
    rintro u ⟨y, hy, hJac⟩
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr
      (lowestProjectionPolynomial_eval_eq_zero_of_regular_root source active n d ell c epsilon (u, y) hy hJac))
  exact (Set.ncard_le_ncard hsub).trans (by
    rw [Set.ncard_coe_finset]
    exact (Multiset.toFinset_card_le p.roots).trans (lowestProjectionPolynomial_roots_card_le source active n d ell c epsilon))

end LeanCanny.ETR.TubeCharacteristicQuotient
