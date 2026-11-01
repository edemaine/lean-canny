/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedHistory
public import LeanCanny.Algebra.IntegralNilpotentParameter

/-! # A fresh formal nilpotent in an actual mixed sampler

The integer birth is X to the already fixed scalar cap. It retains every
older physical coordinate and has a real realization with new value zero,
while its integral prefix keeps the formal nilpotent generator. No claim
is made that a previous coordinate-zero norm polynomial is a pure power.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open LeanCanny.Encoding LeanCanny.Computation IntegralHistorySampler UniformIntegralPrefix Polynomial
open UniformIntegralPowerSchedule
open scoped Classical

noncomputable def nilpotentStep {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) : State P S B (m + 1) (ι ⊕ Unit) where
  sampler := scalarStep x.sampler hm (Nat.two_pow_pos B)
    ((X ^ (2 ^ B) : Polynomial ℤ).map (Int.castRingHom x.sampler.scalarPrefix.carrier)) (2 ^ B)
  bank := x.bank.rootStep hm
    ((X ^ (2 ^ B) : Polynomial ℤ).map (Int.castRingHom x.sampler.scalarPrefix.carrier)) (2 ^ B) 1
  denominator_ne_zero := x.bank.rootStep_denominator_ne_zero hm _ _ _ (by decide) x.denominator_ne_zero
  critical_cap := x.critical_cap

theorem nilpotent_defining_polynomial {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) :
    PaddedIntegralNormalization.polynomial
      ((X ^ (2 ^ B) : Polynomial ℤ).map (Int.castRingHom x.sampler.scalarPrefix.carrier)) (2 ^ B) (2 ^ B) = X ^ (2 ^ B) := by
  rw [Polynomial.map_pow, Polynomial.map_X]
  have H := IntegralNilpotentParameter.purePower_normalization (1 : x.sampler.scalarPrefix.carrier)
    (2 ^ B) (2 ^ B) (Nat.le_refl _)
  simpa only [monomial_one_right_eq_X_pow] using H

theorem nilpotent_real_extend {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S)
    (z : ι → ℝ) (hz : ∀ i, (x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (hφ : ∀ i, φ (x.sampler.scalarPrefix.basis.generator i) = z (x.sampler.scalar i) ^ weights S (2 ^ B) m i) :
    ∃ y : (ι ⊕ Unit) → ℝ,
      (∀ j, ((nilpotentStep x hm).sampler.rows j).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y (Sum.inl i) = z i) ∧
      ∀ ψ : (nilpotentStep x hm).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((nilpotentStep x hm).sampler.scalarPrefix.basis.generator i) =
          y ((nilpotentStep x hm).sampler.scalar i) ^ weights S (2 ^ B) (m + 1) i) →
        ψ ((nilpotentStep x hm).bank.numerator 0) = 0 := by
  have HC : (((X ^ (2 ^ B) : Polynomial ℤ).map (Int.castRingHom x.sampler.scalarPrefix.carrier))).coeff (2 ^ B) = ((1 : ℤ) : x.sampler.scalarPrefix.carrier) := by
    rw [coeff_map, coeff_X_pow, ite_eq_left rfl]
    rfl
  obtain ⟨y, hy, htail, hhead⟩ := scalarStep_real_extend_recover_root_integer x.sampler hm (Nat.two_pow_pos B)
    ((X ^ (2 ^ B) : Polynomial ℤ).map (Int.castRingHom x.sampler.scalarPrefix.carrier)) (2 ^ B) (Nat.le_refl _) 1 (by decide) HC
    z hz φ hφ 0 (by rw [Polynomial.map_map, Polynomial.map_pow, Polynomial.map_X, natDegree_X_pow])
    (Nat.one_le_two_pow) (by simp only [Polynomial.eval₂_map, eval₂_pow, eval₂_X, zero_pow (Nat.two_pow_pos B).ne'])
  refine ⟨y, ?_, htail, ?_⟩
  · exact hy
  · intro ψ hψ
    have H := hhead ψ hψ
    change ψ (AdjoinRoot.root _) = 0
    simp only [Int.cast_one, div_one] at H
    convert H using 1

end LeanCanny.Algebra.IntegralMixedHistory
