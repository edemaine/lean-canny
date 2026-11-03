/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalOptionalPairData

/-! # Optional endpoint pairs with exact native code and chronological provenance -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedChosenLocalRealization IntegralMixedRelativeCuts IntegralMixedCriticalSweep
open IntegralMixedFullHistoryScript IntegralMixedOptionalEndpoints
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem optional_pair (x : State P S B m ι) (hm : m≤S) (hroom : m+1≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(IntegralMixedChronologicalSweepFrame.frame d hk).frozen)
    (HG : g.val=d.labels.length+1)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old : Choices x hm (cutRule x d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ)
    (left right : Endpoint m)
    (HL : left.Allowed (jointEndpointSet x hm φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values old))
    (HR : right.Allowed (jointEndpointSet x hm φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values old)) :
    Nonempty (NativePair x d z φ values left right hn hcap) :=by
  cases left with
  | retained u=>
    cases right with
    | retained v=>
      let R : PairResult x d.frame z φ values (values u) (values v) hn hcap:={
        commands:=[],count:=(by simp),room:=(by simp;omega),codes:=[],code_count:=rfl
        code_size:=(by intro code hc;simp only [List.not_mem_nil] at hc)
        decode:=rfl,tuple:=z,hom:=φ,roots:=hz,old_raw:=fun _=>rfl,old_hom:=(by rfl)
        generators:=hφ,nextValues:=values,quotients:=H,frame:=d.frame
        atomic:=d.atomic,prefixFrozen:=d.prefix_frozen,freeNormal:=d.free_normal
        frozen:=rfl,slice_eq:=rfl,left:=u,right:=v,left_value:=rfl,right_value:=rfl}
      refine ⟨{
        leftSpec:=IntegralMixedRoadmapEndpointSyntax.retainedSpec d u
        rightSpec:=IntegralMixedRoadmapEndpointSyntax.retainedSpec d v,result:=R
        left_good:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_good d u B _ m
        right_good:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_good d v B _ _
        left_fresh:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_fresh d u
        right_fresh:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_fresh d v
        left_producer:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer d u
        right_producer:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer d v
        count:=rfl,codes:=?_,frame:=rfl,left_reference:=?_,right_reference:=?_}⟩
      · simp only [IntegralMixedRoadmapEndpointSyntax.retainedSpec_codes,List.nil_append]
        rfl
      · change u.val=m+0-1-IntegralMixedRoadmapEndpointSyntax.field
          (IntegralMixedRoadmapEndpointSyntax.retainedSpec d u) 1
        rw [IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer]
        have HU:=u.isLt
        omega
      · change v.val=m+0-1-IntegralMixedRoadmapEndpointSyntax.field
          (IntegralMixedRoadmapEndpointSyntax.retainedSpec d v) 1
        rw [IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer]
        have HV:=v.isLt
        omega
    | fresh b=>
      obtain ⟨s,HS⟩:=joint_endpoint x hm hn charge hdegree hcap d hk g hg HG z hz φ hφ values H old b HR
      have KS : IntegralMixedRoadmapEndpointSyntax.field s 0≠0:=by rcases HS.kind with K|K <;> omega
      have FS:=IntegralMixedRoadmapEndpointSyntax.fresh_eq_one KS
      obtain ⟨c,HC,y,ψ,HY,Hold,Hrestrict,Hψ,HV⟩:=HS.encoded
      let code:=IntegralMixedRoadmapEndpointSyntax.code n (IntegralMixedChronologicalFrameCode.labels d) s
      let R : PairResult x d.frame z φ values (values u) b hn hcap:={
        commands:=[c],count:=(by simp),room:=(by simp;omega),codes:=[code],code_count:=rfl
        code_size:=(by
          intro w hw
          have HE : w=code:=by simpa only [List.mem_singleton] using hw
          subst w
          exact (HS.code_length hk).trans (codeBudget_mono n B m (m+2) (by omega)))
        decode:=⟨rfl,HC⟩,tuple:=y,hom:=ψ,roots:=HY,old_raw:=Hold
        old_hom:=(by change ψ.comp (scalarLift x hm c)=φ;exact Hrestrict)
        generators:=Hψ,nextValues:=Fin.cons b values,quotients:=HV,frame:=d.retain.frame
        atomic:=d.retain.atomic,prefixFrozen:=d.retain.prefix_frozen,freeNormal:=d.retain.free_normal
        frozen:=(by rw [d.frame_retain];rfl),slice_eq:=retained_slice d values b
        left:=u.succ,right:=0,left_value:=rfl,right_value:=rfl}
      refine ⟨{
        leftSpec:=IntegralMixedRoadmapEndpointSyntax.retainedSpec d u,rightSpec:=s,result:=R
        left_good:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_good d u B _ m
        right_good:=?_,left_fresh:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_fresh d u
        right_fresh:=FS,left_producer:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer d u
        right_producer:=HS.producer,count:=rfl,codes:=?_,frame:=rfl,left_reference:=?_,right_reference:=?_}⟩
      · simpa only [IntegralMixedRoadmapEndpointSyntax.retainedSpec_fresh,Nat.add_zero] using HS.checked
      · change [code]=_++_
        rw [IntegralMixedRoadmapEndpointSyntax.retainedSpec_codes,HS.codes,List.nil_append]
      · change u.val+1=m+1-1-IntegralMixedRoadmapEndpointSyntax.field
          (IntegralMixedRoadmapEndpointSyntax.retainedSpec d u) 1
        rw [IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer]
        have HU:=u.isLt
        omega
      · change 0=m+1-1-IntegralMixedRoadmapEndpointSyntax.field s 1
        rw [HS.producer]
        omega
  | fresh a=>
    cases right with
    | retained v=>
      obtain ⟨s,HS⟩:=joint_endpoint x hm hn charge hdegree hcap d hk g hg HG z hz φ hφ values H old a HL
      have KS : IntegralMixedRoadmapEndpointSyntax.field s 0≠0:=by rcases HS.kind with K|K <;> omega
      have FS:=IntegralMixedRoadmapEndpointSyntax.fresh_eq_one KS
      obtain ⟨c,HC,y,ψ,HY,Hold,Hrestrict,Hψ,HV⟩:=HS.encoded
      let code:=IntegralMixedRoadmapEndpointSyntax.code n (IntegralMixedChronologicalFrameCode.labels d) s
      let R : PairResult x d.frame z φ values a (values v) hn hcap:={
        commands:=[c],count:=(by simp),room:=(by simp;omega),codes:=[code],code_count:=rfl
        code_size:=(by
          intro w hw
          have HE : w=code:=by simpa only [List.mem_singleton] using hw
          subst w
          exact (HS.code_length hk).trans (codeBudget_mono n B m (m+2) (by omega)))
        decode:=⟨rfl,HC⟩,tuple:=y,hom:=ψ,roots:=HY,old_raw:=Hold
        old_hom:=(by change ψ.comp (scalarLift x hm c)=φ;exact Hrestrict)
        generators:=Hψ,nextValues:=Fin.cons a values,quotients:=HV,frame:=d.retain.frame
        atomic:=d.retain.atomic,prefixFrozen:=d.retain.prefix_frozen,freeNormal:=d.retain.free_normal
        frozen:=(by rw [d.frame_retain];rfl),slice_eq:=retained_slice d values a
        left:=0,right:=v.succ,left_value:=rfl,right_value:=rfl}
      refine ⟨{
        leftSpec:=s,rightSpec:=IntegralMixedRoadmapEndpointSyntax.retainedSpec d v,result:=R
        left_good:=HS.checked,right_good:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_good d v B _ _
        left_fresh:=FS,right_fresh:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_fresh d v
        left_producer:=HS.producer,right_producer:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer d v
        count:=rfl,codes:=?_,frame:=rfl,left_reference:=?_,right_reference:=?_}⟩
      · change [code]=_++_
        rw [HS.codes,IntegralMixedRoadmapEndpointSyntax.retainedSpec_codes,List.append_nil]
      · change 0=m+1-1-IntegralMixedRoadmapEndpointSyntax.field s 1
        rw [HS.producer]
        omega
      · change v.val+1=m+1-1-IntegralMixedRoadmapEndpointSyntax.field
          (IntegralMixedRoadmapEndpointSyntax.retainedSpec d v) 1
        rw [IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer]
        have HV:=v.isLt
        omega
    | fresh b=>
      obtain ⟨sA,HA⟩:=joint_endpoint x hm hn charge hdegree hcap d hk g hg HG z hz φ hφ values H old a HL
      have KA : IntegralMixedRoadmapEndpointSyntax.field sA 0≠0:=by rcases HA.kind with K|K <;> omega
      have FA:=IntegralMixedRoadmapEndpointSyntax.fresh_eq_one KA
      obtain ⟨cA,HCA,yA,ψA,HYA,HoldA,HRa,HψA,HVA⟩:=HA.encoded
      obtain ⟨sB,HB⟩:=fresh_after x hm hroom hn charge hdegree hcap d hk g hg HG cA
        yA HYA φ ψA HψA values a H HVA old b HR
      have KB : IntegralMixedRoadmapEndpointSyntax.field sB 0≠0:=by rcases HB.kind with K|K <;> omega
      have FB:=IntegralMixedRoadmapEndpointSyntax.fresh_eq_one KB
      have EncB:=HB.encoded
      rw [IntegralMixedRoadmapEndpointSyntax.labels_retain] at EncB
      obtain ⟨cB,HCB,yB,ψB,HYB,HoldB,HRb,HψB,HVB⟩:=EncB
      let codeA:=IntegralMixedRoadmapEndpointSyntax.code n (IntegralMixedChronologicalFrameCode.labels d) sA
      let codeB:=IntegralMixedRoadmapEndpointSyntax.code n (IntegralMixedChronologicalFrameCode.labels d) sB
      have HKB : d.retain.labels.length<n+1:=by rw [d.retain_length];exact hk
      have HsizeB:=HB.code_length HKB
      rw [IntegralMixedRoadmapEndpointSyntax.labels_retain] at HsizeB
      let R : PairResult x d.frame z φ values a b hn hcap:={
        commands:=[cB,cA],count:=(by simp),room:=(by simp;omega),codes:=[codeB,codeA],code_count:=rfl
        code_size:=(by
          intro w hw
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
          rcases hw with rfl|rfl
          · exact HsizeB.trans (codeBudget_mono n B (m+1) (m+2) (by omega))
          · exact (HA.code_length hk).trans (codeBudget_mono n B m (m+2) (by omega)))
        decode:=⟨⟨rfl,HCA⟩,HCB⟩,tuple:=yB,hom:=ψB,roots:=HYB
        old_raw:=fun i=>(HoldB (oldColumn cA i)).trans (HoldA i)
        old_hom:=(by
          change (ψB.comp (scalarLift (step x hm cA) hroom cB)).comp (scalarLift x hm cA)=φ
          exact (congrArg (fun χ=>χ.comp (scalarLift x hm cA)) HRb).trans HRa)
        generators:=HψB,nextValues:=Fin.cons b (Fin.cons a values),quotients:=HVB
        frame:=d.retain.retain.frame,atomic:=d.retain.retain.atomic
        prefixFrozen:=d.retain.retain.prefix_frozen,freeNormal:=d.retain.retain.free_normal
        frozen:=(by rw [d.retain.frame_retain,d.frame_retain];rfl)
        slice_eq:=(retained_slice d.retain (Fin.cons a values) b).trans (retained_slice d values a)
        left:=1,right:=0,left_value:=rfl,right_value:=rfl}
      refine ⟨{
        leftSpec:=sA,rightSpec:=sB,result:=R,left_good:=HA.checked,right_good:=?_
        left_fresh:=FA,right_fresh:=FB,count:=rfl,codes:=?_,frame:=rfl
        left_producer:=HA.producer,right_producer:=HB.producer
        left_reference:=?_,right_reference:=?_}⟩
      · have HC:=(HB.checked.fresh_oldBirth KB m)
        simpa only [IntegralMixedRoadmapEndpointSyntax.labels_retain,FA] using HC
      · have HC:=HB.codes
        rw [IntegralMixedRoadmapEndpointSyntax.labels_retain] at HC
        change [codeA,codeB]=_++_
        rw [HA.codes,HC]
        rfl
      · change 1=m+2-1-IntegralMixedRoadmapEndpointSyntax.field sA 1
        rw [HA.producer]
        omega
      · change 0=m+2-1-IntegralMixedRoadmapEndpointSyntax.field sB 1
        rw [HB.producer]
        omega

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
