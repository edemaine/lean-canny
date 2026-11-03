/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalFreshCutEndpoint
public import LeanCanny.Geometry.IntegralMixedJointSlabEndpointSet
public import LeanCanny.Geometry.IntegralMixedChronologicalFrameFreeze

/-! # Every actual chronological endpoint has a canonical native fresh record

The witness specification emits exactly one record at the current birth.
Its decoded extension retains the same full raw tuple, hom and old bank
values. No arbitrary record code or specialized-degree algorithm is supplied.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedRelativeCuts IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem base_rule (x : State P S B m ι) (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(IntegralMixedChronologicalSweepFrame.frame d hk).frozen)
    (HG : g.val=d.labels.length+1) :
    (IntegralMixedChronologicalSweepFrame.data d hk g g hg hg).rule
      (commonDenominator x) (commonDenominator_ne_zero x)=
      cutRule x d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg :=by
  have HE:=IntegralMixedChronologicalSweepFrame.data_rule x d hk g g hg hg
  have HO : g.val-(d.labels.length+1)=0:=by omega
  rw [HO] at HE
  exact HE.trans rfl

theorem joint_endpoint (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
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
    (a : ℝ) (ha : a∈jointEndpointSet x hm φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values old) :
    ∃ s : List Bool,Fresh x hm hn hcap d z φ values a s :=by
  rcases ha with Hbad|Hcritical
  · obtain ⟨j,Hj⟩:=Hbad
    let r:=cutRule x d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg
    let c:=IntegralMixedSelectedCriticalCuts.kind x hm r φ old j
    have HC:=IntegralMixedSelectedCriticalCuts.kind_valid x hm r φ old j
    have HO : IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedSweepRetarget.tag r c)≤2:=by
      obtain ⟨t,j⟩:=j
      fin_cases t <;> norm_num [c,IntegralMixedSelectedCriticalCuts.kind,
        IntegralMixedSweepRetarget.tag,IntegralMixedCutRecordConstructor.tagIndex]
    exact selected_cut_ofRule x hm hn hcap d hk g hg HG z hz φ hφ values H r
      (base_rule x d hk g hg HG) c HC HO a Hj
  · exact ⟨IntegralMixedRoadmapEndpointSyntax.criticalSpec d,
      critical x hm hn charge hdegree hcap d hk z hz φ hφ values H a Hcritical⟩

/-- This is the literal current selected bad set used by the bounded sweep,
including its frozen-first source representation. Prefix ordering discharges
that representation transport without changing the old hom or tuple. -/
theorem sweep_endpoint (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(IntegralMixedChronologicalSweepFrame.frame d hk).frozen)
    (HG : g.val=d.labels.length+1)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old : Choices (cutSource x d.frame (IntegralMixedChronologicalSweepFrame.next d hk)) hm
      (cutRule x d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ)
    (a : ℝ) (ha : a∈sweepBadReal x hm φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values old) :
    ∃ s : List Bool,Fresh x hm hn hcap d z φ values a s :=by
  have HE:=(IntegralMixedChronologicalSweepFrame.prefix_frozen d hk).sweepBadReal_eq
    (IntegralMixedChronologicalSweepFrame.next d hk) x hm g hg φ values old
  rw [HE] at ha
  exact joint_endpoint x hm hn charge hdegree hcap d hk g hg HG z hz φ hφ values H _ a ha

/-- The endpoint producer is the actual current birth. Old labels retain their
chronological meaning; the new frozen coordinate references the newest root. -/
def childDescriptor (d : Descriptor n m) (hk : d.labels.length<n+1) : Descriptor n (m+1):=
  d.retain.freeze (Fin.last m) (by rw [d.retain_length];exact hk)

theorem childDescriptor_labels (d : Descriptor n m) (hk : d.labels.length<n+1) :
    (childDescriptor d hk).labels=d.labels.map Fin.castSucc++[Fin.last m] :=rfl

theorem childDescriptor_slice (d : Descriptor n m) (hk : d.labels.length<n+1)
    (values : Fin m→ℝ) (a : ℝ) :
    slice P (childDescriptor d hk).frame (Fin.cons a values)=
      slice P d.frame values∩{p | p (IntegralMixedChronologicalSweepFrame.next d hk)=a} :=by
  rw [childDescriptor,Descriptor.freeze_slice,retained_slice]
  apply congrArg (slice P d.frame values∩·)
  ext p
  simp only [Descriptor.retain_length,Fin.val_last,Nat.add_sub_cancel,Nat.sub_self]
  rfl

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
