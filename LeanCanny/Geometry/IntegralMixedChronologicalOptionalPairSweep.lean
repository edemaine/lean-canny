/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalOptionalPair

/-! # Native optional pairs for the literal current exceptional endpoint set -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedChosenLocalRealization IntegralMixedRelativeCuts IntegralMixedCriticalSweep
open IntegralMixedOptionalEndpoints
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem optional_pair_sweep (x : State P S B m ι) (hm : m≤S) (hroom : m+1≤S) (hn : 0<n)
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
    (left right : Endpoint m)
    (HL : left.Allowed (sweepBadReal x hm φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values old))
    (HR : right.Allowed (sweepBadReal x hm φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values old)) :
    Nonempty (NativePair x d z φ values left right hn hcap) :=by
  have HE:=(IntegralMixedChronologicalSweepFrame.prefix_frozen d hk).sweepBadReal_eq
    (IntegralMixedChronologicalSweepFrame.next d hk) x hm g hg φ values old
  rw [HE] at HL HR
  exact optional_pair x hm hroom hn charge hdegree hcap d hk g hg HG z hz φ hφ values H _ left right HL HR

theorem NativePair.native_count {x : State P S B m ι} {d : Descriptor n m} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {left right : Endpoint m}
    {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    (R : NativePair x d z φ values left right hn hcap) :
    R.result.commands.length=IntegralMixedRoadmapEndpointSyntax.fresh R.leftSpec+
      IntegralMixedRoadmapEndpointSyntax.fresh R.rightSpec :=by
  rw [R.left_fresh,R.right_fresh]
  exact R.count

theorem NativePair.word {x : State P S B m ι} {d : Descriptor n m} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {left right : Endpoint m}
    {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    (R : NativePair x d z φ values left right hn hcap) :
    WordList.encode R.result.codes.reverse=WordList.encode
      (IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedChronologicalFrameCode.labels d) R.leftSpec++
        IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedChronologicalFrameCode.labels d) R.rightSpec) :=
  congrArg WordList.encode R.codes

theorem NativePair.reference {x : State P S B m ι} {d : Descriptor n m} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {left right : Endpoint m}
    {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
    (R : NativePair x d z φ values left right hn hcap) (side : Bool) :
    (if side then R.result.right else R.result.left).val=m+R.result.commands.length-1-
      IntegralMixedRoadmapEndpointSyntax.field (if side then R.rightSpec else R.leftSpec) 1 :=by
  cases side
  · exact R.left_reference
  · exact R.right_reference

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
