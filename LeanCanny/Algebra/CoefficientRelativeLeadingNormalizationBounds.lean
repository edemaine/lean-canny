/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ParameterMatrixMassBounds
public import LeanCanny.Algebra.CoefficientRelativeLeadingNormalizationAtInfinity
/-! # A native leading-normalization cutoff from actual matrix entry bounds

The determinant estimate supplies the characteristic-coefficient mass bound.
No coefficient-survival or selected-index guard is an additional input.
Uniform bounds for every stage of a complete interpreter remain separate.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientRelativeLeadingNormalization
open Polynomial ParameterMatrixMassBounds
variable {A B :Type*} [CommRing A] [CommRing B] [Algebra ℤ[X] A] {m N :ℕ}

theorem normalizeAt_map_native_after_matrix_mass
    (b :CoefficientCoordinateBasis ℤ[X] A m N) (c :CoefficientCoordinateBasis ℤ B m N)
    (t :ℤ) (ψ :A→+*B)
    (H :CoefficientCoordinateBasis.Specializes (Polynomial.evalRingHom t) ψ b c)
    (p :A[X]) (d entryBits :ℕ)
    (hEntry :∀r s,coefficientMass (Algebra.leftMulMatrix b.basis (p.coeff d) r s)≤2^entryBits)
    (ht :(2:ℝ)^(characteristicBudget (N^m) entryBits+1)≤(t:ℝ)):
    (normalizeAt b.basis p d (Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly.natTrailingDegree).map ψ=
      IntegralRelativeLeadingNormalization.normalize c.basis (p.map ψ) d:=by
  apply normalizeAt_map_native_after_mass b c t ψ H p d
    (characteristicBudget (N^m) entryBits) _ ht
  intro k
  simpa only [Fintype.card_fun,Fintype.card_fin] using
    charpoly_coefficient_mass (Algebra.leftMulMatrix b.basis (p.coeff d)) entryBits hEntry k

theorem normalizeAt_map_native_after_radius
    (b :CoefficientCoordinateBasis ℤ[X] A m N) (c :CoefficientCoordinateBasis ℤ B m N)
    (R :ℕ) (ψ :A→+*B)
    (H :CoefficientCoordinateBasis.Specializes (Polynomial.evalRingHom ((2:ℤ)^R)) ψ b c)
    (p :A[X]) (d entryBits :ℕ)
    (hEntry :∀r s,coefficientMass (Algebra.leftMulMatrix b.basis (p.coeff d) r s)≤2^entryBits)
    (hR :characteristicBudget (N^m) entryBits+1≤R):
    (normalizeAt b.basis p d (Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly.natTrailingDegree).map ψ=
      IntegralRelativeLeadingNormalization.normalize c.basis (p.map ψ) d:=by
  apply normalizeAt_map_native_after_matrix_mass b c ((2:ℤ)^R) ψ H p d entryBits hEntry
  simpa only [Int.cast_pow,Int.cast_ofNat] using
    (pow_le_pow_right₀ (by norm_num :(1:ℝ)≤2) hR)

theorem normalizeAt_map_native_finBasis_after_radius {w :ℕ}
    (b :CoefficientCoordinateBasis ℤ[X] A m (2^w)) (c :IntegralCoordinateBasis B m (2^w))
    (R :ℕ) (ψ :A→+*B)
    (H :CoefficientCoordinateBasis.Specializes (Polynomial.evalRingHom ((2:ℤ)^R)) ψ b
      (CoefficientCoordinateBasis.ofIntegral c)) (p :A[X]) (d entryBits :ℕ)
    (hEntry :∀r s,coefficientMass (Algebra.leftMulMatrix b.basis (p.coeff d) r s)≤2^entryBits)
    (hR :characteristicBudget ((2^w)^m) entryBits+1≤R):
    (normalizeAt b.basis p d (Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly.natTrailingDegree).map ψ=
      IntegralRelativeLeadingNormalization.normalize c.finBasis (p.map ψ) d:=by
  rw [normalizeAt_map_native_after_radius b (CoefficientCoordinateBasis.ofIntegral c) R ψ H
    p d entryBits hEntry hR]
  simp only [CoefficientCoordinateBasis.ofIntegral,IntegralRelativeLeadingNormalization.normalize,
    IntegralRelativeLeadingNormalization.denominator,IntegralRelativeLeadingNormalization.inverseValue,c.finBasis_charpoly]

end LeanCanny.Algebra.CoefficientRelativeLeadingNormalization
