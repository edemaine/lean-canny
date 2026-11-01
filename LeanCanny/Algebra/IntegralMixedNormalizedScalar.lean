/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedRelativeScalar
public import LeanCanny.Algebra.IntegralRelativeLeadingNormalization

/-! # Actual scalar-only mixed births with algebra-valued leading

The selected branch guard is literal nonvanishing of its specialized top
coefficient. Characteristic-polynomial inverse normalization supplies an
integer leading coefficient without changing the scalar degree. Existing
physical coordinates remain unchanged, and no critical point is required.
The relative source polynomial and its degree cap remain explicit: this
module does not supply the slab construction's three exceptional factors.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open LeanCanny.Encoding LeanCanny.Computation IntegralHistorySampler UniformIntegralPrefix
open UniformIntegralPowerSchedule
open scoped Classical

noncomputable def normalizedScalarPolynomial {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (p : Polynomial x.sampler.scalarPrefix.carrier) (d : ℕ) :=
  IntegralRelativeLeadingNormalization.normalize x.sampler.scalarPrefix.basis.finBasis p d

noncomputable def normalizedScalarLeading {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (p : Polynomial x.sampler.scalarPrefix.carrier) (d : ℕ) :=
  IntegralRelativeLeadingNormalization.denominator x.sampler.scalarPrefix.basis.finBasis (p.coeff d)

noncomputable def normalizedScalarStep {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (p : Polynomial x.sampler.scalarPrefix.carrier) (d : ℕ) :
    State P S B (m + 1) (ι ⊕ Unit) where
  sampler := scalarStep x.sampler hm (Nat.two_pow_pos B) (normalizedScalarPolynomial x p d) d
  bank := x.bank.rootStep hm (normalizedScalarPolynomial x p d) d (normalizedScalarLeading x p d)
  denominator_ne_zero := x.bank.rootStep_denominator_ne_zero hm _ _ _
    (IntegralRelativeLeadingNormalization.denominator_ne_zero x.sampler.scalarPrefix.basis.finBasis (p.coeff d)) x.denominator_ne_zero
  critical_cap := x.critical_cap

theorem normalizedScalar_real_extend {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (p : Polynomial x.sampler.scalarPrefix.carrier) (d : ℕ)
    (hd : p.natDegree ≤ d) (hpos : 1 ≤ d) (hcap : d ≤ 2 ^ B)
    (z : ι → ℝ) (hz : ∀ i, (x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (hφ : ∀ i, φ (x.sampler.scalarPrefix.basis.generator i) = z (x.sampler.scalar i) ^ weights S (2 ^ B) m i)
    (ha : φ (p.coeff d) ≠ 0) (t : ℝ) (ht : p.eval₂ φ.toRingHom t = 0) :
    ∃ y : (ι ⊕ Unit) → ℝ,
      (∀ j, ((normalizedScalarStep x hm p d).sampler.rows j).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y (Sum.inl i) = z i) ∧
      ∀ ψ : (normalizedScalarStep x hm p d).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((normalizedScalarStep x hm p d).sampler.scalarPrefix.basis.generator i) =
          y ((normalizedScalarStep x hm p d).sampler.scalar i) ^ weights S (2 ^ B) (m + 1) i) →
        ψ ((normalizedScalarStep x hm p d).bank.numerator 0) /
          ((normalizedScalarStep x hm p d).bank.denominator 0 : ℝ) = t := by
  exact scalarStep_real_extend_recover_root_integer x.sampler hm (Nat.two_pow_pos B)
    (normalizedScalarPolynomial x p d) d hcap (normalizedScalarLeading x p d)
    (IntegralRelativeLeadingNormalization.denominator_ne_zero x.sampler.scalarPrefix.basis.finBasis (p.coeff d))
    (IntegralRelativeLeadingNormalization.coefficient x.sampler.scalarPrefix.basis.finBasis p d)
    z hz φ hφ t
    (IntegralRelativeLeadingNormalization.specialized_degree x.sampler.scalarPrefix.basis.finBasis p d hd φ)
    hpos ((IntegralRelativeLeadingNormalization.root_iff x.sampler.scalarPrefix.basis.finBasis p d φ ha t).mpr ht)

end LeanCanny.Algebra.IntegralMixedHistory
