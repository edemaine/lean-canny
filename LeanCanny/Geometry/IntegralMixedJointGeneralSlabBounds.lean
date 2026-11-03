/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointEndpointRecordBounds
public import LeanCanny.Geometry.IntegralMixedJointGeneralSlab
/-! # One general slab has a bounded exact three-record realization

Both endpoints belong to the ORIGINAL parent endpoint set. The second
record's full factor, selected validity and fresh actual stored degree are
constructed after the first birth, using proven current-Q covariance.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralHistorySampler UniformIntegralPowerSchedule IntegralMixedChosenLocalRealization
open IntegralMixedFullHistoryScript FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem joint_slab_endpoints_bounded (x : State P S B m ι) (hm : m≤S) (hroom : m+1≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F : Frame n) (HF : FreeNormal F) (HA : AtomicRows F m) (HP : PrefixFrozen F)
    (h : Fin (n+1)) (hh : h∉F.frozen) (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old : IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ)
    (a b : ℝ) (ha : a∈jointEndpointSet x hm φ F h g hg values old)
    (hb : b∈jointEndpointSet x hm φ F h g hg values old) :
    ∃ codeA : List Bool,codeA.length≤IntegralMixedCutRecordConstructor.codeBudget n m B ∧
      ∃ cA : Command P B,
      (IntegralMixedCausalUnitRecordBits.record P hn m codeA hcap).template.command
        (commonDenominator x) (commonDenominator_ne_zero x)=cA ∧
      let x₁:=step x hm cA
      ∃ codeB : List Bool,codeB.length≤IntegralMixedCutRecordConstructor.codeBudget n (m+1) B ∧
        ∃ cB : Command P B,
        (IntegralMixedCausalUnitRecordBits.record P hn (m+1) codeB hcap).template.command
          (commonDenominator x₁) (commonDenominator_ne_zero x₁)=cB ∧
        let born:=step x₁ hroom cB
        ∃ y : NextIndex (NextIndex ι cA) cB→ℝ,∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
          (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
          (∀ i,y (oldColumn cB (oldColumn cA i))=z i) ∧
          (ψ.comp (scalarLift x₁ hroom cB)).comp (scalarLift x hm cA)=φ ∧
          (∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+2) i) ∧
          ∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=
            (Fin.cons b (Fin.cons a values) : Fin (m+2)→ℝ) i :=by
  obtain ⟨codeA,hsizeA,cA,hcodeA,yA,φA,hyA,holdA,hrestrictA,hφA,HvaluesA⟩:=
    joint_endpoint_record_bounded x hm hn charge hdegree hcap F HF HA HP h hh g hg z hz φ hφ values H old a ha
  let x₁:=step x hm cA
  let next:=retainedFrameChoices x hm cA hroom φ φA F h g hg values a H HvaluesA old
  have HB : b∈jointEndpointSet x₁ hroom φA (retained F) h g hg (Fin.cons a values) next:=
    (jointEndpointSet_retained_iff x hm cA hroom φ φA F h g hg values a H HvaluesA old b).mpr hb
  obtain ⟨codeB,hsizeB,cB,hcodeB,yB,φB,hyB,holdB,hrestrictB,hφB,HvaluesB⟩:=
    joint_endpoint_record_bounded x₁ hroom hn charge hdegree hcap (retained F) HF.retained HA.retained HP.retained
      h hh g hg yA hyA φA hφA (Fin.cons a values) HvaluesA next b HB
  refine ⟨codeA,hsizeA,cA,hcodeA,codeB,hsizeB,cB,hcodeB,yB,φB,hyB,?_,?_,hφB,HvaluesB⟩
  · intro i
    exact (holdB (oldColumn cA i)).trans (holdA i)
  · exact (congrArg (fun χ=>χ.comp (scalarLift x hm cA)) hrestrictB).trans hrestrictA

theorem joint_general_slab_bounded (x : State P S B m ι) (hm : m≤S) (hroom : m+2≤S) (hn : 0<n)
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
    ∃ codeA : List Bool,codeA.length≤IntegralMixedCutRecordConstructor.codeBudget n m B ∧
      ∃ cA : Command P B,
      (IntegralMixedCausalUnitRecordBits.record P hn m codeA hcap).template.command
        (commonDenominator x) (commonDenominator_ne_zero x)=cA ∧
      let x₁:=step x hm cA
      ∃ codeB : List Bool,codeB.length≤IntegralMixedCutRecordConstructor.codeBudget n (m+1) B ∧
        ∃ cB : Command P B,
        (IntegralMixedCausalUnitRecordBits.record P hn (m+1) codeB hcap).template.command
          (commonDenominator x₁) (commonDenominator_ne_zero x₁)=cB ∧
        let x₂:=step x₁ (by omega) cB
        let born:=criticalStep x₂ hroom (midpointData HA h g j hg hj).rule
        (WordList.encode [codeA,codeB,(midpointData HA h g j hg hj).code]).length≤jointSlabByteBudget n m B ∧
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
  obtain ⟨codeA,hsizeA,cA,hcodeA,codeB,hsizeB,cB,hcodeB,y₂,φ₂,hy₂,hold₂,hrestrict₂,hφ₂,Hvalues₂⟩:=
    joint_slab_endpoints_bounded x hm (by omega) hn charge hdegree hcap F HF HA HP h hh g hg
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
  have HsizeM : (midpointData HA h g j hg hj).code.length≤IntegralMixedCutRecordConstructor.codeBudget n (m+2) B:=
    (midpointData HA h g j hg hj).code_length.trans
      (IntegralMixedCutRecordConstructor.critical_codeBudget_le n (m+2) B)
  have Hbytes:=joint_slab_code_bytes codeA codeB (midpointData HA h g j hg hj).code hsizeA hsizeB HsizeM
  refine ⟨codeA,hsizeA,cA,hcodeA,codeB,hsizeB,cB,hcodeB,Hbytes,hcodeM,y₃,φ₃,hy₃,?_,hphysical₃,?_,hφ₃,Hvalues₃⟩
  · intro i
    exact (hold₃ (oldColumn cB (oldColumn cA i))).trans (hold₂ i)
  · exact (congrArg (fun χ=>(χ.comp (scalarLift x₁ (by omega) cB)).comp (scalarLift x hm cA)) hrestrict₃).trans hrestrict₂

end LeanCanny.Geometry.IntegralMixedFrozenFrame
