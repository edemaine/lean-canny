/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedOptionalEndpointTrace
/-! # Retained or freshly selected endpoints have one honest joint full prefix -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedFullHistoryScript IntegralMixedChosenLocalRealization
open LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

inductive Endpoint (m : ℕ) where
  | retained (index : Fin m)
  | fresh (value : ℝ)

noncomputable def Endpoint.value {m : ℕ} (values : Fin m→ℝ) : Endpoint m→ℝ
  | .retained i=>values i
  | .fresh a=>a

def Endpoint.freshCount {m : ℕ} : Endpoint m→ℕ
  | .retained _=>0
  | .fresh _=>1

def Endpoint.Allowed {m : ℕ} (E : Set ℝ) : Endpoint m→Prop
  | .retained _=>True
  | .fresh a=>a∈E

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem realize_pair (x : State P S B m ι) (hm : m≤S) (hroom : m+1≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F : Frame n) (HF : FreeNormal F) (HA : AtomicRows F m) (HP : PrefixFrozen F)
    (h : Fin (n+1)) (hh : h∉F.frozen) (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old : IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ)
    (left right : Endpoint m)
    (HL : left.Allowed (jointEndpointSet x hm φ F h g hg values old))
    (HR : right.Allowed (jointEndpointSet x hm φ F h g hg values old)) :
    ∃ R : PairResult x F z φ values (left.value values) (right.value values) hn hcap,
      R.commands.length=left.freshCount+right.freshCount :=by
  cases left with
  | retained u=>
    cases right with
    | retained v=>
      exact ⟨{
        commands:=[]
        count:=(by simp)
        room:=(by simp; omega)
        codes:=[]
        code_count:=rfl
        code_size:=(by intro code hc; simp only [List.not_mem_nil] at hc),
        decode:=rfl
        tuple:=z
        hom:=φ
        roots:=hz
        old_raw:=fun _=>rfl
        old_hom:=(by rfl),
        generators:=hφ
        nextValues:=values
        quotients:=H
        frame:=F
        atomic:=HA
        prefixFrozen:=HP
        freeNormal:=HF,
        frozen:=rfl
        slice_eq:=rfl
        left:=u
        right:=v
        left_value:=rfl
        right_value:=rfl},rfl⟩
    | fresh b=>
      obtain ⟨code,hsize,c,hcode,y,ψ,hy,hold,hrestrict,hψ,Hvalues⟩:=
        joint_endpoint_record_bounded x hm hn charge hdegree hcap F HF HA HP h hh g hg z hz φ hφ values H old b HR
      refine ⟨{
        commands:=[c]
        count:=(by simp)
        room:=(by simp; omega)
        codes:=[code]
        code_count:=rfl
        code_size:=?_
        decode:=⟨rfl,hcode⟩
        tuple:=y
        hom:=ψ
        roots:=hy
        old_raw:=hold
        old_hom:=?_
        generators:=hψ
        nextValues:=Fin.cons b values
        quotients:=Hvalues
        frame:=retained F
        atomic:=HA.retained
        prefixFrozen:=HP.retained
        freeNormal:=HF.retained
        frozen:=rfl
        slice_eq:=slice_retained F values b
        left:=u.succ
        right:=0
        left_value:=rfl
        right_value:=rfl},rfl⟩
      · intro w hw
        have HE : w=code:=by simpa only [List.mem_singleton] using hw
        subst w
        exact hsize.trans (codeBudget_mono n B m (m+2) (by omega))
      · change ψ.comp (scalarLift x hm c)=φ
        exact hrestrict
  | fresh a=>
    cases right with
    | retained v=>
      obtain ⟨code,hsize,c,hcode,y,ψ,hy,hold,hrestrict,hψ,Hvalues⟩:=
        joint_endpoint_record_bounded x hm hn charge hdegree hcap F HF HA HP h hh g hg z hz φ hφ values H old a HL
      refine ⟨{
        commands:=[c]
        count:=(by simp)
        room:=(by simp; omega)
        codes:=[code]
        code_count:=rfl
        code_size:=?_
        decode:=⟨rfl,hcode⟩
        tuple:=y
        hom:=ψ
        roots:=hy
        old_raw:=hold
        old_hom:=?_
        generators:=hψ
        nextValues:=Fin.cons a values
        quotients:=Hvalues
        frame:=retained F
        atomic:=HA.retained
        prefixFrozen:=HP.retained
        freeNormal:=HF.retained
        frozen:=rfl
        slice_eq:=slice_retained F values a
        left:=0
        right:=v.succ
        left_value:=rfl
        right_value:=rfl},rfl⟩
      · intro w hw
        have HE : w=code:=by simpa only [List.mem_singleton] using hw
        subst w
        exact hsize.trans (codeBudget_mono n B m (m+2) (by omega))
      · change ψ.comp (scalarLift x hm c)=φ
        exact hrestrict
    | fresh b=>
      obtain ⟨codeA,hsizeA,cA,hcodeA,codeB,hsizeB,cB,hcodeB,y,ψ,hy,hold,hrestrict,hψ,Hvalues⟩:=
        joint_slab_endpoints_bounded x hm hroom hn charge hdegree hcap F HF HA HP h hh g hg
          z hz φ hφ values H old a b HL HR
      refine ⟨{
        commands:=[cB,cA]
        count:=(by simp)
        room:=(by simp; omega)
        codes:=[codeB,codeA]
        code_count:=rfl
        code_size:=?_
        decode:=⟨⟨rfl,hcodeA⟩,hcodeB⟩
        tuple:=y
        hom:=ψ
        roots:=hy
        old_raw:=hold
        old_hom:=?_
        generators:=hψ
        nextValues:=Fin.cons b (Fin.cons a values)
        quotients:=Hvalues
        frame:=retained (retained F),
        atomic:=HA.retained.retained
        prefixFrozen:=HP.retained.retained
        freeNormal:=HF.retained.retained
        frozen:=rfl
        slice_eq:=?_
        left:=1
        right:=0
        left_value:=rfl
        right_value:=rfl},rfl⟩
      · intro w hw
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl|rfl
        · exact hsizeB.trans (codeBudget_mono n B (m+1) (m+2) (by omega))
        · exact hsizeA.trans (codeBudget_mono n B m (m+2) (by omega))
      · change (ψ.comp (scalarLift (step x hm cA) hroom cB)).comp (scalarLift x hm cA)=φ
        exact hrestrict
      · rw [slice_retained,slice_retained]

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
