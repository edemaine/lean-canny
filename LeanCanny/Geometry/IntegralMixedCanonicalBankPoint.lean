/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedBankCanonical
public import LeanCanny.Geometry.PolynomialSystemRegularity

/-! # The actual bank point of a joint canonical prefix root

A bank numerator is its literal prefix generator. Every joint row root
therefore determines bank coordinates by the fixed coordinate powers and
actual nonzero integer denominators. This point is independent of the
choice of interpreting hom; arbitrary coordinate-annihilator combinations
are not assumed to give joint roots.
-/

@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
open LeanCanny.Algebra IntegralMixedHistory UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def point (x : State P S B m ι) (z : Fin m→ℝ) : Fin m→ℝ :=
  fun i=>z i^weights S (2^B) m i/(x.bank.denominator i:ℝ)

theorem denominator_ne_zero (x : State P S B m ι) (i : Fin m) :
    (x.bank.denominator i:ℝ)≠0 := Int.cast_ne_zero.mpr (x.denominator_ne_zero i)

theorem quotient_eq (x : State P S B m ι) (H : Canonical x)
    (z : Fin m→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z i^weights S (2^B) m i) (i : Fin m) :
    φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=point x z i := by
  rw [H i,hφ i]
  rfl

theorem interprets (x : State P S B m ι) (H : Canonical x) (z : Fin m→ℝ)
    (hz : ∀ i,(x.sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∃ φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z i^weights S (2^B) m i) ∧
      ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=point x z i := by
  obtain ⟨φ,hφ⟩:=x.sampler.scalarPrefix.interpret ℝ z hz
  exact ⟨φ,hφ,quotient_eq x H z φ hφ⟩

theorem hom_independent (x : State P S B m ι) (H : Canonical x) (z : Fin m→ℝ)
    (φ ψ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z i^weights S (2^B) m i)
    (hψ : ∀ i,ψ (x.sampler.scalarPrefix.basis.generator i)=z i^weights S (2^B) m i) :
    ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=ψ (x.bank.numerator i)/(x.bank.denominator i:ℝ) :=
  fun i=>(quotient_eq x H z φ hφ i).trans (quotient_eq x H z ψ hψ i).symm

theorem continuous_point (x : State P S B m ι) : Continuous (point x) := by
  apply continuous_pi
  intro i
  exact ((continuous_apply i).pow (weights S (2^B) m i)).div_const _

end LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
