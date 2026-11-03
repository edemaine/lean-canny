/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealCriticalValues
public import LeanCanny.Geometry.IntegralMixedPrefixCriticalRealization
public import LeanCanny.Encoding.IntegralMixedChosenLocalRealization
/-! # An actual critical-height endpoint has an exact full native record

Membership in the real critical-value set supplies the physical point and
gradients. Prefix ordering and atomic rows compile that point into the
existing decoder, preserving one full old tuple and its interpreting hom.
No analogous assertion is made for an arbitrary annihilator root.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem PrefixFrozen.realCriticalValue_record (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F : Frame n) (HF : FreeNormal F) (HA : AtomicRows F m) (HP : PrefixFrozen F)
    (h : Fin (n+1)) (hh : h∉F.frozen)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (ht : t∈realCriticalValues P (line F h) values h) :
    IntegralMixedChosenLocalRealization.Encoded x hm hn hcap z φ values t
      (HA.pointData h h hh hh).code := by
  obtain ⟨a,ha,hat,hgrad⟩:=(line_realCriticalValues_iff P F values h hh HF t).mp ht
  obtain ⟨_,hcode,y,ψ,hy,hold,_,hrestrict,hψ,hvalues⟩:=
    HP.real_extend_point x hm hn charge hdegree hcap F HA h h hh hh z hz φ hφ values H a ha hgrad
  refine ⟨.critical (HA.pointData h h hh hh).rule,hcode,y,ψ,hy,hold,hrestrict,hψ,?_⟩
  intro i
  simpa only [hat] using hvalues i

end LeanCanny.Geometry.IntegralMixedFrozenFrame
