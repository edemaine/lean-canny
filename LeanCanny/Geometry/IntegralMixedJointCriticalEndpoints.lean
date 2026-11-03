/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealCriticalValues
public import LeanCanny.Geometry.IntegralMixedPrefixCriticalRealization
/-! # Two real critical heights of one parent have a single joint full sample

Both births use the fixed original source and target horizon/width. The
second point belongs to the same original slice, expressed by shifted old
references; its realization extends the first full tuple and hom.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

abbrev CriticalIndex (n : ℕ) (ι : Type):=(ι⊕Variables (n+1))⊕Unit

noncomputable def criticalEndpoint (x : State P S B m ι) (hm : m≤S)
    {F : Frame n} (HA : AtomicRows F m) (h : Fin (n+1)) (hh : h∉F.frozen) :
    State P S B (m+1) (CriticalIndex n ι):=
  criticalStep x hm (HA.pointData h h hh hh).rule

noncomputable def criticalPair (x : State P S B m ι) (hroom : m+1≤S)
    {F : Frame n} (HA : AtomicRows F m) (h : Fin (n+1)) (hh : h∉F.frozen) :
    State P S B (m+2) (CriticalIndex n (CriticalIndex n ι)):=
  criticalEndpoint (criticalEndpoint x (by omega) HA h hh) hroom HA.retained h hh

theorem critical_pair_realize (x : State P S B m ι) (hroom : m+1≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F : Frame n) (HF : FreeNormal F) (HA : AtomicRows F m) (HP : PrefixFrozen F)
    (h : Fin (n+1)) (hh : h∉F.frozen)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a b : ℝ) (ha : a∈realCriticalValues P (line F h) values h)
    (hb : b∈realCriticalValues P (line F h) values h) :
    let hm : m≤S:=by omega
    let x₁:=criticalEndpoint x hm HA h hh
    let x₂:=criticalPair x hroom HA h hh
    (IntegralMixedCausalUnitRecordBits.record P hn m (HA.pointData h h hh hh).code hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)=.critical (HA.pointData h h hh hh).rule ∧
    (IntegralMixedCausalUnitRecordBits.record P hn (m+1) (HA.retained.pointData h h hh hh).code hcap).template.command
      (commonDenominator x₁) (commonDenominator_ne_zero x₁)=.critical (HA.retained.pointData h h hh hh).rule ∧
    ∃ y : CriticalIndex n (CriticalIndex n ι)→ℝ,
    ∃ ψ : x₂.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,(x₂.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀ i,y (Sum.inl (Sum.inl (Sum.inl (Sum.inl i))))=z i) ∧
      (ψ.comp (AdjoinRoot.ofAlgHom ℤ _)).comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀ i,ψ (x₂.sampler.scalarPrefix.basis.generator i)=y (x₂.sampler.scalar i)^weights S (2^B) (m+2) i) ∧
      ∀ i,ψ (x₂.bank.numerator i)/(x₂.bank.denominator i:ℝ)=
        (Fin.cons b (Fin.cons a values) : Fin (m+2)→ℝ) i :=by
  dsimp only
  let hm : m≤S:=by omega
  let x₁:=criticalEndpoint x hm HA h hh
  let x₂:=criticalPair x hroom HA h hh
  obtain ⟨pointA,hA,hAh,hAg⟩:=(line_realCriticalValues_iff P F values h hh HF a).mp ha
  obtain ⟨pointB,hB,hBh,hBg⟩:=(line_realCriticalValues_iff P F values h hh HF b).mp hb
  obtain ⟨_,codeA,y₁,φ₁,hy₁,hold₁,_,hrestrict₁,hφ₁,hvalues₁⟩:=
    HP.real_extend_point x hm hn charge hdegree hcap F HA h h hh hh z hz φ hφ values H pointA hA hAg
  have HV₁ : ∀ i,φ₁ (x₁.bank.numerator i)/(x₁.bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i:=by
    intro i
    simpa only [x₁,criticalEndpoint,IntegralMixedFullHistoryScript.step,hAh] using hvalues₁ i
  have HB₁ : pointB∈slice P (retained F) (Fin.cons a values):=by
    rw [slice_retained]
    exact hB
  obtain ⟨_,codeB,y₂,φ₂,hy₂,hold₂,_,hrestrict₂,hφ₂,hvalues₂⟩:=
    HP.retained.real_extend_point x₁ hroom hn charge hdegree hcap (retained F) HA.retained h h hh hh
      y₁ hy₁ φ₁ hφ₁ (Fin.cons a values) HV₁ pointB HB₁ hBg
  refine ⟨codeA,codeB,y₂,φ₂,hy₂,?_,?_,hφ₂,?_⟩
  · intro i
    exact (hold₂ (Sum.inl (Sum.inl i))).trans (hold₁ i)
  · exact (congrArg (fun χ=>χ.comp (AdjoinRoot.ofAlgHom ℤ _)) hrestrict₂).trans hrestrict₁
  · intro i
    simpa only [x₂,x₁,criticalPair,criticalEndpoint,IntegralMixedFullHistoryScript.step,hBh] using hvalues₂ i

end LeanCanny.Geometry.IntegralMixedFrozenFrame
