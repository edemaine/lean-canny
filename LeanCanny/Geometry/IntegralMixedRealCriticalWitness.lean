/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedBankValueInterpretation
public import LeanCanny.Geometry.IntegralMixedPrefixPointReadback
public import LeanCanny.Geometry.IntegralMixedPrefixCriticalRealization
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealCriticalValues
/-! # Complete joint physical witnesses for actual real critical heights

A witness solves every row of the appended critical command and matches all
parent bank values. The height is read from its powered physical coordinate,
not from an independently chosen root of a scalar annihilator.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

noncomputable def RealCriticalWitness (x : State P S B m ι) (hm : m≤S)
    (F : Frame n) (HA : AtomicRows F m) (h : Fin (n+1)) (hh : h∉F.frozen)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) : Prop :=
  ∃z : ((ι⊕FlatAffineCriticalStage.Variables (n+1))⊕Unit)→ℝ,
    (∀i,((criticalStep x hm (HA.pointData h h hh hh).rule).sampler.rows i).eval₂
      (Int.castRingHom ℝ) z=0) ∧
    (∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=
      IntegralMixedCanonicalBankPoint.point x
        (fun j=>z (Sum.inl (Sum.inl (x.sampler.scalar j)))) i) ∧
    (IntegralMixedCanonicalBankPoint.point (criticalStep x hm (HA.pointData h h hh hh).rule)
      (fun i=>z ((criticalStep x hm (HA.pointData h h hh hh).rule).sampler.scalar i)) 0=
        IntegralMixedCriticalReadback.point (S:=S) (B:=B) (m:=m) z h) ∧
    IntegralMixedCriticalReadback.point (S:=S) (B:=B) (m:=m) z h=t

theorem realCriticalWitness_iff (x : State P S B m ι) (hx : Canonical x)
    (hm : m≤S) (hn : 0<n) (charge : ℕ)
    (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F : Frame n) (HA : AtomicRows F m) (HP : PrefixFrozen F) (HF : FreeNormal F)
    (h : Fin (n+1)) (hh : h∉F.frozen)
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) :
    RealCriticalWitness x hm F HA h hh φ t ↔ t∈realCriticalValues P (line F h) values h :=by
  constructor
  · rintro ⟨y,hy,hmatch,_,ht⟩
    have HC:=IntegralMixedBankValueInterpretation.critical_readback x hx hm
      (HA.pointData h h hh hh).rule y hy φ hmatch
    rw [HA.pointData_rule h h hh hh] at HC
    obtain ⟨ha,hg⟩:=HP.point_readback x hm φ F h h hh hh values H _ HC
    exact (line_realCriticalValues_iff P F values h hh HF t).mpr ⟨_,ha,ht,hg⟩
  · intro ht
    obtain ⟨a,ha,hat,hg⟩:=(line_realCriticalValues_iff P F values h hh HF t).mp ht
    obtain ⟨_,_,y,ψ,hy,hold,hphysical,_,hψ,hvalues⟩:=
      HP.real_extend_point x hm hn charge hdegree hcap F HA h h hh hh z hz φ hφ values H a ha hg
    refine ⟨y,hy,?_,?_,(hphysical h).trans hat⟩
    · intro i
      change φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=
        y (Sum.inl (Sum.inl (x.sampler.scalar i)))^weights S (2^B) m i/(x.bank.denominator i:ℝ)
      rw [hold]
      exact IntegralMixedCanonicalBankPoint.quotient_eq x hx _ φ hφ i
    · exact (IntegralMixedCanonicalBankPoint.quotient_eq _
        (criticalStep_canonical x hx hm _) _ ψ hψ 0).symm.trans
          ((hvalues 0).trans (hphysical h).symm)

theorem realCriticalFreeInterval_iff (x : State P S B m ι) (hx : Canonical x)
    (hm : m≤S) (hn : 0<n) (charge : ℕ)
    (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F : Frame n) (HA : AtomicRows F m) (HP : PrefixFrozen F) (HF : FreeNormal F)
    (h : Fin (n+1)) (hh : h∉F.frozen)
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a b : ℝ) :
    Disjoint (Set.Ioo a b) (realCriticalValues P (line F h) values h) ↔
      ¬∃t∈Set.Ioo a b,RealCriticalWitness x hm F HA h hh φ t :=by
  have HE:=realCriticalWitness_iff x hx hm hn charge hdegree hcap F HA HP HF h hh z hz φ hφ values H
  rw [Set.disjoint_left]
  constructor
  · intro HD ⟨t,ht,hw⟩
    exact HD ht ((HE t).mp hw)
  · intro HN t ht hc
    exact HN ⟨t,ht,(HE t).mpr hc⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrame
