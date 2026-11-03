/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointSlabEndpoints
public import LeanCanny.Geometry.IntegralMixedJointCriticalSlab
public import LeanCanny.Geometry.IntegralMixedJointMidpointSound
/-! # Three actual records realize both general slab endpoints and one anchor

All endpoint membership refers to ONE original parent cut set. The literal
midpoint frame uses scale two and the sum of the two new retained refs.
The anchor is a real physical source/frozen/gradient witness, not merely an
elimination root. One final full tuple and hom retain every value.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralHistorySampler UniformIntegralPowerSchedule IntegralMixedChosenLocalRealization
open IntegralMixedFullHistoryScript FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem joint_general_slab (x : State P S B m ι) (hm : m≤S) (hroom : m+2≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F : Frame n) (HF : FreeNormal F) (HA : AtomicRows F m) (HP : PrefixFrozen F)
    (h g j : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old : IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ)
    (a b : ℝ) (ha : a∈jointEndpointSet x hm φ F h g hg values old)
    (hb : b∈jointEndpointSet x hm φ F h g hg values old)
    (point : Fin (n+1)→ℝ) (hpoint : point∈slice P F values) (hmid : point h=(a+b)/2)
    (hgradient : ∀ i,i∉(line F h).frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) point=0) :
    ∃ codeA : List Bool,∃ cA : Command P B,
      (IntegralMixedCausalUnitRecordBits.record P hn m codeA hcap).template.command
        (commonDenominator x) (commonDenominator_ne_zero x)=cA ∧
      let x₁:=step x hm cA
      ∃ codeB : List Bool,∃ cB : Command P B,
        (IntegralMixedCausalUnitRecordBits.record P hn (m+1) codeB hcap).template.command
          (commonDenominator x₁) (commonDenominator_ne_zero x₁)=cB ∧
        let x₂:=step x₁ (by omega) cB
        let born:=criticalStep x₂ hroom (midpointData HA h g j hg hj).rule
        (IntegralMixedCausalUnitRecordBits.record P hn (m+2) (midpointData HA h g j hg hj).code hcap).template.command
          (commonDenominator x₂) (commonDenominator_ne_zero x₂)=.critical (midpointData HA h g j hg hj).rule ∧
        ∃ y : CriticalIndex n (NextIndex (NextIndex ι cA) cB)→ℝ,
        ∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
          (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
          (∀ i,y (Sum.inl (Sum.inl (oldColumn cB (oldColumn cA i))))=z i) ∧
          (∀ i,y (Sum.inl (ambient i))^physical S (2^B) (m+2)=point i) ∧
          ((ψ.comp (AdjoinRoot.ofAlgHom ℤ _)).comp (scalarLift x₁ (by omega) cB)).comp (scalarLift x hm cA)=φ ∧
          (∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+3) i) ∧
          ∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=
            (Fin.cons (point j) (Fin.cons b (Fin.cons a values)) : Fin (m+3)→ℝ) i :=by
  obtain ⟨codeA,cA,hcodeA,codeB,cB,hcodeB,y₂,φ₂,hy₂,hold₂,hrestrict₂,hφ₂,Hvalues₂⟩:=
    joint_slab_endpoints x hm (by omega) hn charge hdegree hcap F HF HA HP h hh g hg
      z hz φ hφ values H old a b ha hb
  let x₁:=step x hm cA
  let x₂:=step x₁ (show m+1≤S from by omega) cB
  have HM : point∈slice P (midpointFrame HA h) (Fin.cons b (Fin.cons a values)):=by
    rw [midpointFrame_slice HA h hh values a b]
    exact ⟨hpoint,hmid⟩
  obtain ⟨_,hcodeM,y₃,φ₃,hy₃,hold₃,hphysical₃,hrestrict₃,hφ₃,Hvalues₃⟩:=
    (HP.midpointFrame HA h hfirst hh).real_extend_original_point x₂ hroom hn charge hdegree hcap
      (insert h F.frozen) (midpointDouble h) (midpointRows HA h) g j hg hj
      y₂ hy₂ φ₂ hφ₂ (Fin.cons b (Fin.cons a values)) Hvalues₂ point HM hgradient
  refine ⟨codeA,cA,hcodeA,codeB,cB,hcodeB,hcodeM,y₃,φ₃,hy₃,?_,hphysical₃,?_,hφ₃,Hvalues₃⟩
  · intro i
    exact (hold₃ (oldColumn cB (oldColumn cA i))).trans (hold₂ i)
  · exact (congrArg (fun χ=>(χ.comp (scalarLift x₁ (by omega) cB)).comp (scalarLift x hm cA)) hrestrict₃).trans hrestrict₂

theorem joint_general_record_count (codeA codeB codeM : List Bool) :
    [codeA,codeB,codeM].length=3 :=rfl

theorem nextIndex_card_le (c : Command P B) :
    Fintype.card (NextIndex ι c)≤Fintype.card ι+(2*n+4) :=by
  cases c <;> simp only [NextIndex,Fintype.card_sum,Fintype.card_unit,Variables,Fintype.card_fin] <;> omega

theorem joint_general_physical_columns (cA cB : Command P B) :
    Fintype.card (CriticalIndex n (NextIndex (NextIndex ι cA) cB))≤Fintype.card ι+3*(2*n+4) :=by
  have HA:=nextIndex_card_le (ι:=ι) cA
  have HB:=nextIndex_card_le (ι:=NextIndex ι cA) cB
  simp only [CriticalIndex,Fintype.card_sum,Fintype.card_unit,Variables,Fintype.card_fin]
  omega

end LeanCanny.Geometry.IntegralMixedFrozenFrame
