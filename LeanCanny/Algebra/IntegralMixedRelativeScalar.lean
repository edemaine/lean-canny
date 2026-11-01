/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedHistorySemantics

/-! # Scalar-only births for roots of bounded relative critical polynomials

Every real root of the specialized relative polynomial can be retained
without adjoining a physical critical sample. This includes extraneous
roots of that relative polynomial and preserves the actual older point.
It does not identify the three exceptional-factor classes used by the
slab construction with this particular relative polynomial.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open LeanCanny.Encoding LeanCanny.Computation IntegralHistorySampler UniformIntegralPrefix
open UniformIntegralPowerSchedule
open scoped Classical

noncomputable def relativeScalarStep {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) : State P S B (m + 1) (ι ⊕ Unit) where
  sampler := scalarStep x.sampler hm (Nat.two_pow_pos B) (criticalPolynomial x hm r) (criticalDegree x hm r)
  bank := x.bank.rootStep hm (criticalPolynomial x hm r) (criticalDegree x hm r) (criticalLeading x hm r)
  denominator_ne_zero := x.bank.rootStep_denominator_ne_zero hm _ _ _ (criticalLeading_ne_zero x hm r) x.denominator_ne_zero
  critical_cap := x.critical_cap

theorem criticalPolynomial_specialized_degree {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    ((criticalPolynomial x hm r).map φ.toRingHom).natDegree = criticalDegree x hm r := by
  have HE := IntegralHistoryCriticalBits.annihilator_eq (family x hm r) []
  have H := CoordinateFrozenCriticalElimination.specialized_degree φ.toRingHom
    (data x hm r).degree (by have H := P.degree_two; change 0 < P.degree; omega)
    (data x hm r).scales (data x hm r).scales_ne (data x hm r).heights r.offset.val
    ((family x hm r).fit [])
    ((data x hm r).low.map (Int.castRingHom x.sampler.scalarPrefix.carrier))
    ((data x hm r).leading : x.sampler.scalarPrefix.carrier)
    (by rw [map_intCast]; exact Int.cast_ne_zero.mpr P.leading_ne_zero)
    ((family x hm r).objective []) ((family x hm r).coordinate [])
  have HP : criticalPolynomial x hm r = _ := HE
  rw [HP]
  exact H

theorem relativeScalar_real_extend {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n)
    (z : ι → ℝ) (hz : ∀ i, (x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (hφ : ∀ i, φ (x.sampler.scalarPrefix.basis.generator i) = z (x.sampler.scalar i) ^ weights S (2 ^ B) m i)
    (t : ℝ) (ht : (criticalPolynomial x hm r).eval₂ φ.toRingHom t = 0) :
    ∃ y : (ι ⊕ Unit) → ℝ,
      (∀ j, ((relativeScalarStep x hm r).sampler.rows j).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y (Sum.inl i) = z i) ∧
      ∀ ψ : (relativeScalarStep x hm r).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((relativeScalarStep x hm r).sampler.scalarPrefix.basis.generator i) =
          y ((relativeScalarStep x hm r).sampler.scalar i) ^ weights S (2 ^ B) (m + 1) i) →
        ψ ((relativeScalarStep x hm r).bank.numerator 0) /
          ((relativeScalarStep x hm r).bank.denominator 0 : ℝ) = t := by
  apply scalarStep_real_extend_recover_root_integer x.sampler hm (Nat.two_pow_pos B)
    (criticalPolynomial x hm r) (criticalDegree x hm r) (criticalDegree_cap x hm r)
    (criticalLeading x hm r) (criticalLeading_ne_zero x hm r) (criticalLeading_coefficient x hm r)
    z hz φ hφ t (criticalPolynomial_specialized_degree x hm r φ) _ ht
  exact Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by decide : 1 ≤ 2))

theorem relativeScalar_real_extend_recover {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n)
    (z : ι → ℝ) (hz : ∀ i, (x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (hφ : ∀ i, φ (x.sampler.scalarPrefix.basis.generator i) = z (x.sampler.scalar i) ^ weights S (2 ^ B) m i)
    (values : Fin m → ℝ)
    (H : ∀ i, φ (x.bank.numerator i) / (x.bank.denominator i : ℝ) = values i)
    (t : ℝ) (ht : (criticalPolynomial x hm r).eval₂ φ.toRingHom t = 0) :
    ∃ y : (ι ⊕ Unit) → ℝ, ∃ ψ : (relativeScalarStep x hm r).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
      (∀ j, ((relativeScalarStep x hm r).sampler.rows j).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y (Sum.inl i) = z i) ∧
      (∀ i, ψ ((relativeScalarStep x hm r).sampler.scalarPrefix.basis.generator i) =
        y ((relativeScalarStep x hm r).sampler.scalar i) ^ weights S (2 ^ B) (m + 1) i) ∧
      ∀ i, ψ ((relativeScalarStep x hm r).bank.numerator i) /
        ((relativeScalarStep x hm r).bank.denominator i : ℝ) = (show Fin (m + 1) → ℝ from Fin.cons t values) i := by
  obtain ⟨y, hy, htail, hhead⟩ := relativeScalar_real_extend x hm r z hz φ hφ t ht
  obtain ⟨ψ, hψ⟩ := (relativeScalarStep x hm r).sampler.interpret ℝ y hy
  have hrestrict : ψ.comp (AdjoinRoot.ofAlgHom ℤ _) = φ := by
    apply x.sampler.scalarPrefix.basis.algHom_ext
    intro i
    have HI := hψ i.succ
    change ψ (AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator i)) =
      y (Sum.inl (x.sampler.scalar i)) ^ weights S (2 ^ B) (m + 1) i.succ at HI
    rw [UniformIntegralPowerSchedule.old, htail] at HI
    exact HI.trans (hφ i).symm
  refine ⟨y, ψ, hy, htail, hψ, fun i => Fin.cases (hhead ψ hψ) (fun j => ?_) i⟩
  change ψ (AdjoinRoot.of _ (x.bank.numerator j)) / (x.bank.denominator j : ℝ) = values j
  have HE : ψ (AdjoinRoot.of _ (x.bank.numerator j)) = φ (x.bank.numerator j) :=
    congrArg (fun χ => χ (x.bank.numerator j)) hrestrict
  rw [HE]
  exact H j

end LeanCanny.Algebra.IntegralMixedHistory
