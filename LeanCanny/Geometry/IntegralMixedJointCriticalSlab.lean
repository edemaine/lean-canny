/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointCriticalEndpoints
public import LeanCanny.Geometry.IntegralMixedJointMidpointFrame
/-! # One slab's two critical endpoints and midpoint anchor share one full tuple

The endpoints are genuine real critical heights of ONE parent slice. The
midpoint anchor is a real selected physical point; its source, midpoint
equation and free gradients are explicit geometric hypotheses. Three
actual decoded records suffice at a fixed target horizon and width.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

noncomputable def midpointData {F : Frame n} (HA : AtomicRows F m) (h g j : Fin (n+1))
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen) :=
  originalPointData (insert h F.frozen) (midpointDouble h) (midpointRows HA h) g j hg hj

noncomputable def criticalSlab (x : State P S B m ι) (hroom : m+2≤S)
    {F : Frame n} (HA : AtomicRows F m) (h g j : Fin (n+1))
    (hh : h∉F.frozen) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen) :
    State P S B (m+3) (CriticalIndex n (CriticalIndex n (CriticalIndex n ι))) :=
  criticalStep (criticalPair x (by omega) HA h hh) hroom (midpointData HA h g j hg hj).rule

theorem critical_slab_realize (x : State P S B m ι) (hroom : m+2≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F : Frame n) (HF : FreeNormal F) (HA : AtomicRows F m) (HP : PrefixFrozen F)
    (h g j : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a b : ℝ) (ha : a∈realCriticalValues P (line F h) values h)
    (hb : b∈realCriticalValues P (line F h) values h)
    (point : Fin (n+1)→ℝ) (hpoint : point∈slice P F values) (hmid : point h=(a+b)/2)
    (hgradient : ∀ i,i∉(line F h).frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) point=0) :
    let x₁:=criticalEndpoint x (by omega) HA h hh
    let x₂:=criticalPair x (by omega) HA h hh
    let born:=criticalSlab x hroom HA h g j hh hg hj
    (IntegralMixedCausalUnitRecordBits.record P hn m (HA.pointData h h hh hh).code hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)=.critical (HA.pointData h h hh hh).rule ∧
    (IntegralMixedCausalUnitRecordBits.record P hn (m+1) (HA.retained.pointData h h hh hh).code hcap).template.command
      (commonDenominator x₁) (commonDenominator_ne_zero x₁)=.critical (HA.retained.pointData h h hh hh).rule ∧
    (IntegralMixedCausalUnitRecordBits.record P hn (m+2) (midpointData HA h g j hg hj).code hcap).template.command
      (commonDenominator x₂) (commonDenominator_ne_zero x₂)=.critical (midpointData HA h g j hg hj).rule ∧
    ∃ y : CriticalIndex n (CriticalIndex n (CriticalIndex n ι))→ℝ,
    ∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀ i,y (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl i))))))=z i) ∧
      (∀ i,y (Sum.inl (ambient i))^physical S (2^B) (m+2)=point i) ∧
      ((ψ.comp (AdjoinRoot.ofAlgHom ℤ _)).comp (AdjoinRoot.ofAlgHom ℤ _)).comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+3) i) ∧
      ∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=
        (Fin.cons (point j) (Fin.cons b (Fin.cons a values)) : Fin (m+3)→ℝ) i :=by
  dsimp only
  let x₁:=criticalEndpoint x (by omega) HA h hh
  let x₂:=criticalPair x (by omega) HA h hh
  let born:=criticalSlab x hroom HA h g j hh hg hj
  obtain ⟨codeA,codeB,y₂,φ₂,hy₂,hold₂,hrestrict₂,hφ₂,Hvalues₂⟩:=
    critical_pair_realize x (by omega) hn charge hdegree hcap F HF HA HP h hh z hz φ hφ values H a b ha hb
  have HM : point∈slice P (midpointFrame HA h) (Fin.cons b (Fin.cons a values)):=by
    rw [midpointFrame_slice HA h hh values a b]
    exact ⟨hpoint,hmid⟩
  obtain ⟨_,codeM,y₃,φ₃,hy₃,hold₃,hphysical₃,hrestrict₃,hφ₃,Hvalues₃⟩:=
    (HP.midpointFrame HA h hfirst hh).real_extend_original_point x₂ hroom hn charge hdegree hcap
      (insert h F.frozen) (midpointDouble h) (midpointRows HA h) g j hg hj
      y₂ hy₂ φ₂ hφ₂ (Fin.cons b (Fin.cons a values)) Hvalues₂ point HM hgradient
  refine ⟨codeA,codeB,codeM,y₃,φ₃,hy₃,?_,hphysical₃,?_,hφ₃,Hvalues₃⟩
  · intro i
    exact (hold₃ (Sum.inl (Sum.inl (Sum.inl (Sum.inl i))))).trans (hold₂ i)
  · exact (congrArg (fun χ=>(χ.comp (AdjoinRoot.ofAlgHom ℤ _)).comp (AdjoinRoot.ofAlgHom ℤ _)) hrestrict₃).trans hrestrict₂

end LeanCanny.Geometry.IntegralMixedFrozenFrame
