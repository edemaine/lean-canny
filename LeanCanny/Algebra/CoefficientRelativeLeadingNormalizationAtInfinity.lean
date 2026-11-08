/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientRelativeLeadingNormalizationSpecialization
public import LeanCanny.Algebra.IntegralParameterInverseAtInfinity
/-! # Integer specialization of the actual normalizer beyond a common mass bound

A bound on the characteristic-coefficient parameter polynomials supplies the
fixed-index guards. This does not construct a uniform recursive presentation
or bound the masses of all interpreter stages.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientRelativeLeadingNormalization
open Polynomial
open scoped Classical
variable {A B :Type*} [CommRing A] [CommRing B] [Algebra ℤ[X] A] {m N :ℕ}

private theorem integer_survivor (q :ℤ[X]) (hq :q≠0) (b :ℕ)
    (hb :coefficientMass q≤2^b) (t :ℤ) (ht :(2:ℝ)^(b+1)≤(t:ℝ)) :q.eval t≠0:=by
  have H:=IntegralParameterInverseAtInfinity.nonzero_after_mass q hq b hb (t:ℝ) ht
  change q.eval₂ (Int.castRingHom ℝ) ((Int.castRingHom ℝ) t)≠0 at H
  rw [Polynomial.eval₂_at_apply] at H
  exact Int.cast_ne_zero.mp H

theorem normalizeAt_map_native_after_mass
    (b :CoefficientCoordinateBasis ℤ[X] A m N) (c :CoefficientCoordinateBasis ℤ B m N)
    (t :ℤ) (ψ :A→+*B)
    (H :CoefficientCoordinateBasis.Specializes (Polynomial.evalRingHom t) ψ b c)
    (p :A[X]) (d massBits :ℕ)
    (hMass :∀k,coefficientMass ((Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly.coeff k)≤2^massBits)
    (ht :(2:ℝ)^(massBits+1)≤(t:ℝ)) :
    (normalizeAt b.basis p d (Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly.natTrailingDegree).map ψ=
      IntegralRelativeLeadingNormalization.normalize c.basis (p.map ψ) d:=by
  apply normalizeAt_map_native H
  · intro k hk
    rw [coeff_eq_zero_of_lt_natTrailingDegree hk,map_zero]
  · exact integer_survivor _
      (Polynomial.trailingCoeff_ne_zero.mpr (Matrix.charpoly_monic _).ne_zero)
      massBits (hMass _) t ht

theorem normalizeAt_map_native_finBasis_after_mass {w :ℕ}
    (b :CoefficientCoordinateBasis ℤ[X] A m (2^w)) (c :IntegralCoordinateBasis B m (2^w))
    (t :ℤ) (ψ :A→+*B)
    (H :CoefficientCoordinateBasis.Specializes (Polynomial.evalRingHom t) ψ b
      (CoefficientCoordinateBasis.ofIntegral c)) (p :A[X]) (d massBits :ℕ)
    (hMass :∀k,coefficientMass ((Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly.coeff k)≤2^massBits)
    (ht :(2:ℝ)^(massBits+1)≤(t:ℝ)) :
    (normalizeAt b.basis p d (Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly.natTrailingDegree).map ψ=
      IntegralRelativeLeadingNormalization.normalize c.finBasis (p.map ψ) d:=by
  rw [normalizeAt_map_native_after_mass b (CoefficientCoordinateBasis.ofIntegral c) t ψ H p d massBits hMass ht]
  simp only [CoefficientCoordinateBasis.ofIntegral,
    IntegralRelativeLeadingNormalization.normalize,
    IntegralRelativeLeadingNormalization.denominator,
    IntegralRelativeLeadingNormalization.inverseValue,c.finBasis_charpoly]

end LeanCanny.Algebra.CoefficientRelativeLeadingNormalization
