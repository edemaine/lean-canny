/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChosenLocalRealization
/-! # Constructed local records retain their actual guard receipts

A critical scalar is correlated with its own powered physical block. A cut
retains selected validity, the exact stored degree and the untruncated factor
root. These facts are constructed from the original local choices, rather
than inferred from an arbitrary decoded or full-row realization.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChosenLocalRealization
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedRelativeCuts
open IntegralMixedFullHistoryScript IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]

noncomputable def Guard (x :State P S B m ι) (hm :m≤S)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c :Command P B) (a :ℝ)
    (y :NextIndex ι c→ℝ) :Prop:=
  match c with
  | .integer _ _ _=>False
  | .critical r=>
    y (Sum.inl (FlatAffineCriticalStage.ambient
      (ClearedCoordinateCritical.freeIndex r.offset.val ((family x hm r).fit []).le
        ((family x hm r).coordinate []))))^physical S (2^B) m=a
  | .cut r k d _ _=>Valid x hm r φ k ∧ d=selectedDegree x hm r φ k ∧
      (factor x hm r k).eval₂ φ.toRingHom a=0

structure Receipt (x :State P S B m ι) (hm :m≤S) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z :ι→ℝ) (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values :Fin m→ℝ) (a :ℝ) (code :List Bool) where
  command :Command P B
  decode :(IntegralMixedCausalUnitRecordBits.record P hn m code hcap).template.command
    (commonDenominator x) (commonDenominator_ne_zero x)=command
  tuple :NextIndex ι command→ℝ
  hom :(step x hm command).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ
  roots :∀i,((step x hm command).sampler.rows i).eval₂ (Int.castRingHom ℝ) tuple=0
  old_raw :∀i,tuple (oldColumn command i)=z i
  old_hom :hom.comp (scalarLift x hm command)=φ
  generators :∀i,hom ((step x hm command).sampler.scalarPrefix.basis.generator i)=
    tuple ((step x hm command).sampler.scalar i)^weights S (2^B) (m+1) i
  quotients :∀i,hom ((step x hm command).bank.numerator i)/
    ((step x hm command).bank.denominator i:ℝ)=(Fin.cons a values :Fin (m+1)→ℝ) i
  guard :Guard x hm φ command a tuple

theorem Receipt.encoded {x :State P S B m ι} {hm :m≤S} {hn :0<n}
    {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    {z :ι→ℝ} {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ}
    {a :ℝ} {code :List Bool} (r :Receipt x hm hn hcap z φ values a code) :
    Encoded x hm hn hcap z φ values a code:=
  ⟨r.command,r.decode,r.tuple,r.hom,r.roots,r.old_raw,r.old_hom,r.generators,r.quotients⟩

theorem critical_receipt (x :State P S B m ι) (hm :m≤S) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (w :CriticalChoice x hm φ) :
    Nonempty (Receipt x hm hn hcap z φ values (w.value x hm φ) w.record.code):=by
  obtain ⟨hc,y,ψ,hy,hold,hphysical,hrestrict,hψ,hvalues⟩:=
    IntegralMixedCriticalRecordConstructor.real_extend_record x hm hn w.record w.charge w.degree_eq hcap
      z hz φ hφ values H w.point w.frozen w.zero w.gradient
  exact ⟨⟨.critical w.record.rule,hc,y,ψ,hy,hold,hrestrict,hψ,hvalues,hphysical _⟩⟩

theorem cut_receipt (x :State P S B m ι) (hm :m≤S) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (w :CutChoice x hm φ) :
    Nonempty (Receipt x hm hn hcap z φ values w.value (w.code x hm φ)):=by
  let r:=w.record.rule (commonDenominator x) (commonDenominator_ne_zero x)
  let j:=IntegralMixedSweepRetarget.coordinateIndex r w.kind
  let rr:=IntegralMixedSweepRetarget.rule r j
  let cc:=IntegralMixedSweepRetarget.kind r j w.kind
  let d:=selectedDegree x hm rr φ cc
  have hd:=selectedDegree_bound x hm rr φ cc
  have he:=IntegralMixedSweepRetarget.selectedDegree_eq x hm r j φ w.kind
  have HC:=IntegralMixedCutRecordConstructor.chosen_command w.record P (commonDenominator x)
    (commonDenominator_ne_zero x) w.kind d hd hcap
  have Hcode :w.code x hm φ=w.record.chosenCode (commonDenominator x)
      (commonDenominator_ne_zero x) w.kind d:=by
    unfold CutChoice.code
    rw [←he]
  have HD :(IntegralMixedCausalUnitRecordBits.record P hn m (w.code x hm φ) hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)=.cut rr cc d hd (hd.trans hcap):=by
    rw [Hcode]
    exact HC
  obtain ⟨_,y,ψ,hy,hold,hrestrict,hψ,hvalues⟩:=IntegralMixedSweepRetarget.real_extend_shared_coordinate
    x hm r φ w.kind w.valid hcap z hz hφ values H w.value w.root
  refine ⟨⟨.cut rr cc d hd (hd.trans hcap),HD,y,ψ,hy,hold,hrestrict,hψ,hvalues,?_⟩⟩
  change Valid x hm rr φ cc ∧ d=selectedDegree x hm rr φ cc ∧
    (factor x hm rr cc).eval₂ φ.toRingHom w.value=0
  refine ⟨(IntegralMixedSweepRetarget.valid_iff x hm r j φ w.kind).mpr w.valid,rfl,?_⟩
  rw [IntegralMixedSweepRetarget.factor_eq]
  exact w.root

theorem realize_receipt (x :State P S B m ι) (hm :m≤S) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (w :Choice x hm φ) :
    Nonempty (Receipt x hm hn hcap z φ values (w.value x hm φ) (w.code x hm φ)):=by
  cases w with
  | inl w=>exact critical_receipt x hm hn hcap z hz φ hφ values H w
  | inr w=>exact cut_receipt x hm hn hcap z hz φ hφ values H w

end LeanCanny.Encoding.IntegralMixedChosenLocalRealization
