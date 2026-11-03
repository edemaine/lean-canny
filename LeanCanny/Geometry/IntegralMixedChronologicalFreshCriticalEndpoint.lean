/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalEndpointSpec
public import LeanCanny.Geometry.IntegralMixedPrefixOriginalPointRealization
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealCriticalValues
public import LeanCanny.Encoding.IntegralMixedChosenLocalRealization

/-! # A critical endpoint realizes the exact canonical chronological code -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedChosenLocalRealization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

/-- The semantic extension is tied to the native endpoint specification's
literal code, not to a separately chosen byteword. -/
structure Fresh (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d : Descriptor n m) (z : ι→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (a : ℝ) (s : List Bool) : Prop where
  checked : IntegralMixedRoadmapEndpointSyntax.Good n B
    (IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree) m m
      (IntegralMixedChronologicalFrameCode.labels d) s
  kind : IntegralMixedRoadmapEndpointSyntax.field s 0=1 ∨ IntegralMixedRoadmapEndpointSyntax.field s 0=2
  producer : IntegralMixedRoadmapEndpointSyntax.field s 1=m
  encoded : Encoded x hm hn hcap z φ values a
    (IntegralMixedRoadmapEndpointSyntax.code n (IntegralMixedChronologicalFrameCode.labels d) s)

theorem Fresh.codes {x : State P S B m ι} {hm : m≤S} {hn : 0<n}
    {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    {d : Descriptor n m} {z : ι→ℝ} {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ}
    {values : Fin m→ℝ} {a : ℝ} {s : List Bool} (H : Fresh x hm hn hcap d z φ values a s) :
    IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedChronologicalFrameCode.labels d) s=
      [IntegralMixedRoadmapEndpointSyntax.code n (IntegralMixedChronologicalFrameCode.labels d) s] :=by
  have HK : IntegralMixedRoadmapEndpointSyntax.field s 0≠0:=by rcases H.kind with H|H <;> omega
  exact ite_eq_right HK

theorem Fresh.word {x : State P S B m ι} {hm : m≤S} {hn : 0<n}
    {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    {d : Descriptor n m} {z : ι→ℝ} {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ}
    {values : Fin m→ℝ} {a : ℝ} {s : List Bool} (H : Fresh x hm hn hcap d z φ values a s) :
    IntegralMixedRoadmapEndpointSyntax.word n (IntegralMixedChronologicalFrameCode.labels d) s=
      WordList.encode [IntegralMixedRoadmapEndpointSyntax.code n (IntegralMixedChronologicalFrameCode.labels d) s] :=by
  exact congrArg WordList.encode H.codes

theorem critical (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d : Descriptor n m) (hk : d.labels.length<n+1)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : ℝ) (ha : a∈realCriticalValues P (line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)) values
      (IntegralMixedChronologicalSweepFrame.next d hk)) :
    Fresh x hm hn hcap d z φ values a (IntegralMixedRoadmapEndpointSyntax.criticalSpec d) :=by
  let h:=IntegralMixedChronologicalSweepFrame.next d hk
  have hh : h∉d.frame.frozen:=IntegralMixedChronologicalSweepFrame.next_free d hk
  obtain ⟨p,hp,hpa,hgrad⟩:=(line_realCriticalValues_iff P d.frame values h hh d.free_normal a).mp ha
  obtain ⟨_,HC,y,ψ,HY,Hold,_,HR,Hψ,HV⟩:=
    PrefixFrozen.real_extend_original_point x hm hn charge hdegree hcap
      d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) d.prefix_frozen h h hh hh
      z hz φ hφ values H p hp hgrad
  refine ⟨IntegralMixedRoadmapEndpointSyntax.criticalSpec_good d B _ m,Or.inl ?_,?_,?_⟩
  · exact IntegralMixedRoadmapEndpointSyntax.field_spec_0 _ _ _ _ _ _
  · exact IntegralMixedRoadmapEndpointSyntax.field_spec_1 _ _ _ _ _ _
  · rw [IntegralMixedRoadmapEndpointSyntax.criticalSpec_code]
    change Encoded x hm hn hcap z φ values a
      (IntegralMixedChronologicalFrameCode.code n (IntegralMixedChronologicalFrameCode.labels d) h.val h.val)
    rw [←IntegralMixedChronologicalFrameCode.data_code d h h hh hh]
    refine ⟨.critical (IntegralMixedChronologicalFrameCode.data d h h hh hh).rule,HC,
      y,ψ,HY,Hold,HR,Hψ,?_⟩
    intro i
    simpa only [IntegralMixedChronologicalFrameCode.data,hpa] using HV i

theorem retained_slice (d : Descriptor n m) (values : Fin m→ℝ) (a : ℝ) :
    slice P d.retain.frame (Fin.cons a values)=slice P d.frame values :=by
  rw [d.frame_retain,slice_retained]

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
