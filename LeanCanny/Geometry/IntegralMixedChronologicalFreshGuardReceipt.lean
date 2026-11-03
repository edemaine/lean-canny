/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalFreshEndpoint
public import LeanCanny.Encoding.IntegralMixedChosenLocalGuardReceipt
/-! # Canonical fresh endpoint specifications keep the constructed guard tuple -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedChosenLocalRealization IntegralMixedRelativeCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]

structure FreshReceipt (x :State P S B m ι) (hm :m≤S) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d :Descriptor n m) (z :ι→ℝ) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values :Fin m→ℝ) (a :ℝ) (s :List Bool) where
  checked :IntegralMixedRoadmapEndpointSyntax.Good n B
    (IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree) m m
      (IntegralMixedChronologicalFrameCode.labels d) s
  kind :IntegralMixedRoadmapEndpointSyntax.field s 0=1 ∨ IntegralMixedRoadmapEndpointSyntax.field s 0=2
  producer :IntegralMixedRoadmapEndpointSyntax.field s 1=m
  receipt :Receipt x hm hn hcap z φ values a
    (IntegralMixedRoadmapEndpointSyntax.code n (IntegralMixedChronologicalFrameCode.labels d) s)

theorem FreshReceipt.fresh {x :State P S B m ι} {hm :m≤S} {hn :0<n}
    {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    {d :Descriptor n m} {z :ι→ℝ} {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ}
    {values :Fin m→ℝ} {a :ℝ} {s :List Bool} (r :FreshReceipt x hm hn hcap d z φ values a s) :
    Fresh x hm hn hcap d z φ values a s:=⟨r.checked,r.kind,r.producer,r.receipt.encoded⟩

omit [Fintype ι] in
private theorem selected_index (x :State P S B m ι) (hm :m≤S) (d :Descriptor n m)
    (g j :Fin (n+1)) (hg :g∉d.frame.frozen) (hj :j∉d.frame.frozen) :
    ClearedCoordinateCritical.freeIndex
      (IntegralMixedChronologicalFrameCode.data d g j hg hj).rule.offset.val
      ((family x hm (IntegralMixedChronologicalFrameCode.data d g j hg hj).rule).fit []).le
      ((family x hm (IntegralMixedChronologicalFrameCode.data d g j hg hj).rule).coordinate [])=j:=by
  rw [IntegralMixedChronologicalFrameCode.data_rule]
  have HI:=pointRule_index d.frame g hg j hj
  rw [d.prefix_frozen.permutation] at HI
  exact HI

theorem critical_guard_receipt (x :State P S B m ι) (hm :m≤S) (hn :0<n)
    (charge :ℕ) (hdegree :P.degree=BoundedZeroSource.powerDegree charge)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d :Descriptor n m) (hk :d.labels.length<n+1)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a :ℝ) (ha :a∈realCriticalValues P (line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)) values
      (IntegralMixedChronologicalSweepFrame.next d hk)) :
    Nonempty (FreshReceipt x hm hn hcap d z φ values a (IntegralMixedRoadmapEndpointSyntax.criticalSpec d)):=by
  let h:=IntegralMixedChronologicalSweepFrame.next d hk
  have hh :h∉d.frame.frozen:=IntegralMixedChronologicalSweepFrame.next_free d hk
  obtain ⟨p,hp,hpa,hgrad⟩:=(line_realCriticalValues_iff P d.frame values h hh d.free_normal a).mp ha
  obtain ⟨_,HC,y,ψ,HY,Hold,Hphysical,HR,Hψ,HV⟩:=
    PrefixFrozen.real_extend_original_point x hm hn charge hdegree hcap
      d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) d.prefix_frozen h h hh hh
      z hz φ hφ values H p hp hgrad
  refine ⟨⟨IntegralMixedRoadmapEndpointSyntax.criticalSpec_good d B _ m,
    Or.inl (IntegralMixedRoadmapEndpointSyntax.field_spec_0 _ _ _ _ _ _),
    IntegralMixedRoadmapEndpointSyntax.field_spec_1 _ _ _ _ _ _,?_⟩⟩
  rw [IntegralMixedRoadmapEndpointSyntax.criticalSpec_code]
  change Receipt x hm hn hcap z φ values a
    (IntegralMixedChronologicalFrameCode.code n (IntegralMixedChronologicalFrameCode.labels d) h.val h.val)
  rw [←IntegralMixedChronologicalFrameCode.data_code d h h hh hh]
  refine ⟨.critical (IntegralMixedChronologicalFrameCode.data d h h hh hh).rule,HC,
    y,ψ,HY,Hold,HR,Hψ,?_,?_⟩
  · intro i
    simpa only [IntegralMixedChronologicalFrameCode.data,hpa] using HV i
  · change y (Sum.inl (FlatAffineCriticalStage.ambient _))^physical S (2^B) m=a
    rw [Hphysical,selected_index x hm d h h hh hh]
    exact hpa

theorem selected_cut_guard_receipt (x :State P S B m ι) (hm :m≤S) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d :Descriptor n m) (hk :d.labels.length<n+1)
    (g :Fin (n+1)) (hg :g∉(IntegralMixedChronologicalSweepFrame.frame d hk).frozen)
    (HG :g.val=d.labels.length+1)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (c :Kind P ((IntegralMixedChronologicalSweepFrame.data d hk g g hg hg).rule
      (commonDenominator x) (commonDenominator_ne_zero x)))
    (hc :Valid x hm _ φ c)
    (hordinary :IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedSweepRetarget.tag _ c)≤2)
    (a :ℝ) (ha :(factor x hm _ c).eval₂ φ.toRingHom a=0) :
    ∃s :List Bool,Nonempty (FreshReceipt x hm hn hcap d z φ values a s):=by
  let D:=IntegralMixedChronologicalSweepFrame.data d hk g g hg hg
  let r:=D.rule (commonDenominator x) (commonDenominator_ne_zero x)
  let degree:=selectedDegree x hm r φ c
  let j:=IntegralMixedChronologicalCutCode.physicalCoordinate d hk g hg
    (D.coordinate (commonDenominator x) (commonDenominator_ne_zero x) c)
  let tag:=IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedSweepRetarget.tag r c)
  let choice:=IntegralMixedSweepRetarget.choiceIndex r c
  let s:=IntegralMixedRoadmapEndpointSyntax.cutSpec d j.val tag choice degree
  let w :CutChoice x hm φ:=⟨D,c,hc,a,ha⟩
  have Hcode :IntegralMixedRoadmapEndpointSyntax.code n (IntegralMixedChronologicalFrameCode.labels d) s=
      w.code x hm φ:=by
    have HC:=IntegralMixedChronologicalCutCode.chosenCode_actual d hk g hg P
      (commonDenominator x) (commonDenominator_ne_zero x) c degree
    have HGcode:=congrArg (fun t :ℕ=>IntegralMixedChronologicalCutCode.code n
      (IntegralMixedChronologicalFrameCode.labels d) t j.val tag choice degree) HG
    exact (IntegralMixedRoadmapEndpointSyntax.cutSpec_code d j.val tag choice degree).trans
      (HGcode.symm.trans HC.symm)
  have HJ :d.labels.length+1≤j.val:=
    (IntegralMixedChronologicalSweepFrame.free_iff d hk j).mp
      (IntegralMixedChronologicalCutCode.physicalCoordinate_free d hk g hg _)
  have HB :IntegralMixedChronologicalCutCode.Bounds n m B
      (IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree)
      (IntegralMixedChronologicalFrameCode.labels d) (d.labels.length+1) j.val tag choice degree:=by
    refine ⟨⟨IntegralMixedChronologicalFrameCode.labels_good d,?_,?_,?_,j.isLt⟩,
      hordinary,(IntegralMixedCutRecordConstructor.choice_le P r c).trans hcap,selectedDegree_bound x hm r φ c⟩
    · rw [IntegralMixedChronologicalFrameCode.labels_count]
    · exact HG ▸ g.isLt
    · simpa only [IntegralMixedChronologicalFrameCode.labels_count] using HJ
  obtain ⟨R⟩:=cut_receipt x hm hn hcap z hz φ hφ values H w
  refine ⟨s,⟨⟨IntegralMixedRoadmapEndpointSyntax.cutSpec_good d B _ m j.val tag choice degree HB,
    Or.inr (IntegralMixedRoadmapEndpointSyntax.field_spec_0 _ _ _ _ _ _),
    IntegralMixedRoadmapEndpointSyntax.field_spec_1 _ _ _ _ _ _,?_⟩⟩⟩
  rw [Hcode]
  exact R

theorem selected_cut_guard_ofRule (x :State P S B m ι) (hm :m≤S) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d :Descriptor n m) (hk :d.labels.length<n+1)
    (g :Fin (n+1)) (hg :g∉(IntegralMixedChronologicalSweepFrame.frame d hk).frozen)
    (HG :g.val=d.labels.length+1)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (r :IntegralMixedCriticalSweep.Rule n)
    (hr :(IntegralMixedChronologicalSweepFrame.data d hk g g hg hg).rule
      (commonDenominator x) (commonDenominator_ne_zero x)=r)
    (c :Kind P r) (hc :Valid x hm r φ c)
    (hordinary :IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedSweepRetarget.tag r c)≤2)
    (a :ℝ) (ha :(factor x hm r c).eval₂ φ.toRingHom a=0) :
    ∃s :List Bool,Nonempty (FreshReceipt x hm hn hcap d z φ values a s):=by
  subst r
  exact selected_cut_guard_receipt x hm hn hcap d hk g hg HG z hz φ hφ values H c hc hordinary a ha

theorem joint_endpoint_guard_receipt (x :State P S B m ι) (hm :m≤S) (hn :0<n)
    (charge :ℕ) (hdegree :P.degree=BoundedZeroSource.powerDegree charge)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d :Descriptor n m) (hk :d.labels.length<n+1)
    (g :Fin (n+1)) (hg :g∉(IntegralMixedChronologicalSweepFrame.frame d hk).frozen)
    (HG :g.val=d.labels.length+1)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old :Choices x hm (IntegralMixedFrozenFrame.cutRule x d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ)
    (a :ℝ) (ha :a∈jointEndpointSet x hm φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values old) :
    ∃s :List Bool,Nonempty (FreshReceipt x hm hn hcap d z φ values a s):=by
  rcases ha with Hbad|Hcritical
  · obtain ⟨j,Hj⟩:=Hbad
    let r:=IntegralMixedFrozenFrame.cutRule x d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg
    let c:=LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.kind x hm r φ old j
    have HC:=LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.kind_valid x hm r φ old j
    have HO :IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedSweepRetarget.tag r c)≤2:=by
      obtain ⟨t,j⟩:=j
      fin_cases t <;> norm_num [c,LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.kind,
        IntegralMixedSweepRetarget.tag,IntegralMixedCutRecordConstructor.tagIndex]
    exact selected_cut_guard_ofRule x hm hn hcap d hk g hg HG z hz φ hφ values H r
      (base_rule x d hk g hg HG) c HC HO a Hj
  · exact ⟨IntegralMixedRoadmapEndpointSyntax.criticalSpec d,
      critical_guard_receipt x hm hn charge hdegree hcap d hk z hz φ hφ values H a Hcritical⟩

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
