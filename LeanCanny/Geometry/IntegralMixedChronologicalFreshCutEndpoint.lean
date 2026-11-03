/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalFreshCriticalEndpoint
public import LeanCanny.Encoding.IntegralMixedChronologicalChosenCutCode

/-! # A chosen ordinary factor root realizes the exact fresh endpoint ABI

The specialized degree is a bounded witness stored in the native record.
Its computation is not assumed polynomial time.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedChosenLocalRealization IntegralMixedRelativeCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem selected_cut (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(IntegralMixedChronologicalSweepFrame.frame d hk).frozen)
    (HG : g.val=d.labels.length+1)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (c : Kind P ((IntegralMixedChronologicalSweepFrame.data d hk g g hg hg).rule
      (commonDenominator x) (commonDenominator_ne_zero x)))
    (hc : Valid x hm _ φ c)
    (hordinary : IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedSweepRetarget.tag _ c)≤2)
    (a : ℝ) (ha : (factor x hm _ c).eval₂ φ.toRingHom a=0) :
    ∃ s : List Bool,Fresh x hm hn hcap d z φ values a s ∧
      IntegralMixedRoadmapEndpointSyntax.field s 0=2 ∧
      IntegralMixedRoadmapEndpointSyntax.field s 5=selectedDegree x hm _ φ c ∧
      (IntegralMixedRoadmapEndpointSyntax.code n (IntegralMixedChronologicalFrameCode.labels d) s).length≤
        IntegralMixedCutRecordConstructor.codeBudget n m B :=by
  let D:=IntegralMixedChronologicalSweepFrame.data d hk g g hg hg
  let r:=D.rule (commonDenominator x) (commonDenominator_ne_zero x)
  let degree:=selectedDegree x hm r φ c
  let j:=IntegralMixedChronologicalCutCode.physicalCoordinate d hk g hg
    (D.coordinate (commonDenominator x) (commonDenominator_ne_zero x) c)
  let tag:=IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedSweepRetarget.tag r c)
  let choice:=IntegralMixedSweepRetarget.choiceIndex r c
  let s:=IntegralMixedRoadmapEndpointSyntax.cutSpec d j.val tag choice degree
  let w : CutChoice x hm φ:=⟨D,c,hc,a,ha⟩
  have Hcode : IntegralMixedRoadmapEndpointSyntax.code n (IntegralMixedChronologicalFrameCode.labels d) s=
      w.code x hm φ :=by
    have HC:=IntegralMixedChronologicalCutCode.chosenCode_actual d hk g hg P
      (commonDenominator x) (commonDenominator_ne_zero x) c degree
    have HGcode:=congrArg (fun t : ℕ=>IntegralMixedChronologicalCutCode.code n
      (IntegralMixedChronologicalFrameCode.labels d) t j.val tag choice degree) HG
    exact (IntegralMixedRoadmapEndpointSyntax.cutSpec_code d j.val tag choice degree).trans
      (HGcode.symm.trans HC.symm)
  have HJ : d.labels.length+1≤j.val:=
    (IntegralMixedChronologicalSweepFrame.free_iff d hk j).mp
      (IntegralMixedChronologicalCutCode.physicalCoordinate_free d hk g hg _)
  have Hbounds : IntegralMixedChronologicalCutCode.Bounds n m B
      (IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree)
      (IntegralMixedChronologicalFrameCode.labels d) (d.labels.length+1) j.val tag choice degree:=by
    refine ⟨⟨IntegralMixedChronologicalFrameCode.labels_good d,?_,?_,?_,j.isLt⟩,
      hordinary,(IntegralMixedCutRecordConstructor.choice_le P r c).trans hcap,
      selectedDegree_bound x hm r φ c⟩
    · rw [IntegralMixedChronologicalFrameCode.labels_count]
    · exact HG ▸ g.isLt
    · simpa only [IntegralMixedChronologicalFrameCode.labels_count] using HJ
  refine ⟨s,⟨IntegralMixedRoadmapEndpointSyntax.cutSpec_good d B _ m j.val tag choice degree Hbounds,
    Or.inr ?_,?_,?_⟩,?_,?_,?_⟩
  · exact IntegralMixedRoadmapEndpointSyntax.field_spec_0 _ _ _ _ _ _
  · exact IntegralMixedRoadmapEndpointSyntax.field_spec_1 _ _ _ _ _ _
  · rw [Hcode]
    exact IntegralMixedChosenLocalRealization.cut x hm hn hcap z hz φ hφ values H w
  · exact IntegralMixedRoadmapEndpointSyntax.field_spec_0 _ _ _ _ _ _
  · exact IntegralMixedRoadmapEndpointSyntax.field_spec_5 _ _ _ _ _ _
  · rw [Hcode]
    exact w.code_length x hm φ hcap

theorem selected_cut_ofRule (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(IntegralMixedChronologicalSweepFrame.frame d hk).frozen)
    (HG : g.val=d.labels.length+1)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (r : IntegralMixedCriticalSweep.Rule n)
    (hr : (IntegralMixedChronologicalSweepFrame.data d hk g g hg hg).rule
      (commonDenominator x) (commonDenominator_ne_zero x)=r)
    (c : Kind P r) (hc : Valid x hm r φ c)
    (hordinary : IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedSweepRetarget.tag r c)≤2)
    (a : ℝ) (ha : (factor x hm r c).eval₂ φ.toRingHom a=0) :
    ∃ s : List Bool,Fresh x hm hn hcap d z φ values a s :=by
  subst r
  obtain ⟨s,HS,_,_,_⟩:=selected_cut x hm hn hcap d hk g hg HG z hz φ hφ values H c hc hordinary a ha
  exact ⟨s,HS⟩

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
