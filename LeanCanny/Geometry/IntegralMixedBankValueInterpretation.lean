/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
public import LeanCanny.Geometry.IntegralMixedCriticalReadback
/-! # Retained quotient agreement fixes the actual older interpretation

The integer denominators belong to one fixed parent state. Equality of all
bank quotients determines its generators, including for nonreduced algebras.
No equality of a later clearing denominator with the parent is used.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedBankValueInterpretation
open LeanCanny.Algebra IntegralMixedHistory UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem hom_ext (x : State P S B m ι) (hx : Canonical x)
    (φ ψ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (h : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=
      ψ (x.bank.numerator i)/(x.bank.denominator i:ℝ)) : φ=ψ :=by
  apply x.sampler.scalarPrefix.basis.algHom_ext
  intro i
  have HD : (x.bank.denominator i:ℝ)≠0:=Int.cast_ne_zero.mpr (x.denominator_ne_zero i)
  have HE:=congrArg (fun v : ℝ=>v*(x.bank.denominator i:ℝ)) (h i)
  rw [div_mul_cancel₀ _ HD,div_mul_cancel₀ _ HD,hx i] at HE
  exact HE

theorem generators (x : State P S B m ι) (hx : Canonical x)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : Fin m→ℝ)
    (h : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=
      IntegralMixedCanonicalBankPoint.point x z i) :
    ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z i^weights S (2^B) m i :=by
  intro i
  have HD : (x.bank.denominator i:ℝ)≠0:=Int.cast_ne_zero.mpr (x.denominator_ne_zero i)
  have HE:=congrArg (fun v : ℝ=>v*(x.bank.denominator i:ℝ)) (h i)
  unfold IntegralMixedCanonicalBankPoint.point at HE
  rw [div_mul_cancel₀ _ HD,div_mul_cancel₀ _ HD,hx i] at HE
  exact HE

theorem critical_readback [Fintype ι] (x : State P S B m ι) (hx : Canonical x)
    (hm : m≤S) (r : CriticalRule n)
    (z : ((ι⊕FlatAffineCriticalStage.Variables (n+1))⊕Unit)→ℝ)
    (hz : ∀i,((criticalStep x hm r).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (h : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=
      IntegralMixedCanonicalBankPoint.point x
        (fun j=>z (Sum.inl (Sum.inl (x.sampler.scalar j)))) i) :
    IntegralMixedCriticalReadback.CriticalPoint x hm r φ
      (IntegralMixedCriticalReadback.point (S:=S) (B:=B) (m:=m) z) :=
  IntegralMixedCriticalReadback.roots_for_interpretation x hm r z hz φ
    (generators x hx φ _ h)

end LeanCanny.Geometry.IntegralMixedBankValueInterpretation
