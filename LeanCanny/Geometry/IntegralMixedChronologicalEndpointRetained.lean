/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalFreshEndpoint
public import LeanCanny.Encoding.IntegralMixedChronologicalOptionalEndpointSpec

/-! # Exact chronological frames and native endpoint codes after retention -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedChosenLocalRealization IntegralMixedRelativeCuts IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

def retainMany (d : Descriptor n m) : (q : ℕ)→Descriptor n (m+q)
  | 0=>d
  | q+1=>(retainMany d q).retain

theorem retainMany_labels (d : Descriptor n m) (q : ℕ) :
    IntegralMixedChronologicalFrameCode.labels (retainMany d q)=IntegralMixedChronologicalFrameCode.labels d :=by
  induction q with
  | zero=>rfl
  | succ q ih=>exact (IntegralMixedRoadmapEndpointSyntax.labels_retain _).trans ih

theorem Fresh.code_length {x : State P S B m ι} {hm : m≤S} {hn : 0<n}
    {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    {d : Descriptor n m} (hk : d.labels.length<n+1) {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {a : ℝ} {s : List Bool}
    (H : Fresh x hm hn hcap d z φ values a s) :
    (IntegralMixedRoadmapEndpointSyntax.code n (IntegralMixedChronologicalFrameCode.labels d) s).length≤
      IntegralMixedCutRecordConstructor.codeBudget n m B :=by
  have HK : WordListRecords.count (IntegralMixedChronologicalFrameCode.labels d)<n+1:=by
    rw [IntegralMixedChronologicalFrameCode.labels_count];exact hk
  rcases IntegralMixedRoadmapEndpointSyntax.checked_code H.checked
      (IntegralMixedChronologicalFrameCode.labels_good d) le_rfl HK with HR|HC|HC
  · rcases H.kind with Hk|Hk <;> omega
  · rw [HC.2.2.2]
    rw [←IntegralMixedChronologicalFrameCode.rawData_code n m _ _ _ HC.2.2.1]
    exact (IntegralMixedCriticalRecordConstructor.Data.code_length _).trans
      (IntegralMixedCutRecordConstructor.critical_codeBudget_le n m B)
  · rw [HC.2.2.2]
    exact IntegralMixedChronologicalCutCode.raw_code_size n m B _ _ _ _ _ _ HC.2.2.1.1
      HC.2.2.1.2.1 HC.2.2.1.2.2.1 (HC.2.2.1.2.2.2.trans hcap)

theorem joint_endpoint_at (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d : Descriptor n m) (hk : d.labels.length<n+1)
    (F : Frame n) (h g : Fin (n+1)) (hd : d.frame=F) (Hh : h.val=d.labels.length)
    (hg : g∉(line F h).frozen) (HG : g.val=d.labels.length+1)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old : Choices x hm (cutRule x F h g hg) φ)
    (a : ℝ) (ha : a∈jointEndpointSet x hm φ F h g hg values old) :
    ∃ s : List Bool,Fresh x hm hn hcap d z φ values a s :=by
  subst F
  have HH : h=IntegralMixedChronologicalSweepFrame.next d hk:=Fin.ext Hh
  subst h
  exact joint_endpoint x hm hn charge hdegree hcap d hk g hg HG z hz φ hφ values H old a ha

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
