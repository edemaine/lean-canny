/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointEndpointRecord
/-! # Two arbitrary actual slab endpoints are retained on one full tuple

Both endpoints belong to the ORIGINAL parent endpoint set. The second
record's full factor, selected validity and fresh actual stored degree are
constructed after the first birth, using proven current-Q covariance.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralHistorySampler UniformIntegralPowerSchedule IntegralMixedChosenLocalRealization
open IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem joint_slab_endpoints (x : State P S B m ι) (hm : m≤S) (hroom : m+1≤S) (hn : 0<n)
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
    ∃ codeA : List Bool,∃ cA : Command P B,
      (IntegralMixedCausalUnitRecordBits.record P hn m codeA hcap).template.command
        (commonDenominator x) (commonDenominator_ne_zero x)=cA ∧
      let x₁:=step x hm cA
      ∃ codeB : List Bool,∃ cB : Command P B,
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
  obtain ⟨codeA,cA,hcodeA,yA,φA,hyA,holdA,hrestrictA,hφA,HvaluesA⟩:=
    joint_endpoint_record x hm hn charge hdegree hcap F HF HA HP h hh g hg z hz φ hφ values H old a ha
  let x₁:=step x hm cA
  let next:=retainedFrameChoices x hm cA hroom φ φA F h g hg values a H HvaluesA old
  have HB : b∈jointEndpointSet x₁ hroom φA (retained F) h g hg (Fin.cons a values) next:=
    (jointEndpointSet_retained_iff x hm cA hroom φ φA F h g hg values a H HvaluesA old b).mpr hb
  obtain ⟨codeB,cB,hcodeB,yB,φB,hyB,holdB,hrestrictB,hφB,HvaluesB⟩:=
    joint_endpoint_record x₁ hroom hn charge hdegree hcap (retained F) HF.retained HA.retained HP.retained
      h hh g hg yA hyA φA hφA (Fin.cons a values) HvaluesA next b HB
  refine ⟨codeA,cA,hcodeA,codeB,cB,hcodeB,yB,φB,hyB,?_,?_,hφB,HvaluesB⟩
  · intro i
    exact (holdB (oldColumn cA i)).trans (holdA i)
  · exact (congrArg (fun χ=>χ.comp (scalarLift x hm cA)) hrestrictB).trans hrestrictA

end LeanCanny.Geometry.IntegralMixedFrozenFrame
