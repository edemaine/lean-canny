/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalEndpointRetained
public import LeanCanny.Geometry.IntegralMixedOptionalSlabEndpoints

/-! # Literal native specifications retained by an actual optional endpoint pair -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedChosenLocalRealization IntegralMixedRelativeCuts IntegralMixedCriticalSweep
open IntegralMixedFullHistoryScript IntegralMixedOptionalEndpoints
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

structure NativePair (x : State P S B m ι) (d : Descriptor n m)
    (z : ι→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : Fin m→ℝ)
    (left right : Endpoint m) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) where
  leftSpec : List Bool
  rightSpec : List Bool
  result : PairResult x d.frame z φ values (left.value values) (right.value values) hn hcap
  left_good : IntegralMixedRoadmapEndpointSyntax.Good n B
    (IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree) m m
      (IntegralMixedChronologicalFrameCode.labels d) leftSpec
  right_good : IntegralMixedRoadmapEndpointSyntax.Good n B
    (IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree) m
      (m+IntegralMixedRoadmapEndpointSyntax.fresh leftSpec)
      (IntegralMixedChronologicalFrameCode.labels d) rightSpec
  left_fresh : IntegralMixedRoadmapEndpointSyntax.fresh leftSpec=left.freshCount
  right_fresh : IntegralMixedRoadmapEndpointSyntax.fresh rightSpec=right.freshCount
  left_producer : IntegralMixedRoadmapEndpointSyntax.field leftSpec 1=
    match left with | .retained i=>m-1-i.val | .fresh _=>m
  right_producer : IntegralMixedRoadmapEndpointSyntax.field rightSpec 1=
    match right with | .retained i=>m-1-i.val | .fresh _=>m+left.freshCount
  count : result.commands.length=left.freshCount+right.freshCount
  codes : result.codes.reverse=
    IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedChronologicalFrameCode.labels d) leftSpec++
      IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedChronologicalFrameCode.labels d) rightSpec
  frame : result.frame=(retainMany d result.commands.length).frame
  left_reference : result.left.val=m+result.commands.length-1-
    IntegralMixedRoadmapEndpointSyntax.field leftSpec 1
  right_reference : result.right.val=m+result.commands.length-1-
    IntegralMixedRoadmapEndpointSyntax.field rightSpec 1

/-- Actual left-birth quotient recovery transports the ORIGINAL endpoint set
to the fresh right source. Both current-Q factors and real critical values
are transported; no emitted-code equality or hom constancy is assumed. -/
theorem fresh_after (x : State P S B m ι) (hm : m≤S) (hnext : m+1≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(IntegralMixedChronologicalSweepFrame.frame d hk).frozen)
    (HG : g.val=d.labels.length+1) (c : Command P B)
    (z : NextIndex ι c→ℝ) (hz : ∀ i,((step x hm c).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : (step x hm c).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hψ : ∀ i,ψ ((step x hm c).sampler.scalarPrefix.basis.generator i)=
      z ((step x hm c).sampler.scalar i)^weights S (2^B) (m+1) i)
    (values : Fin m→ℝ) (a : ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (HN : ∀ i,ψ ((step x hm c).bank.numerator i)/((step x hm c).bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i)
    (old : Choices x hm (cutRule x d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ)
    (b : ℝ) (hb : b∈jointEndpointSet x hm φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values old) :
    ∃ s : List Bool,Fresh (step x hm c) hnext hn hcap d.retain z ψ (Fin.cons a values) b s :=by
  let h:=IntegralMixedChronologicalSweepFrame.next d hk
  let next:=retainedFrameChoices x hm c hnext φ ψ d.frame h g hg values a H HN old
  have HB : b∈jointEndpointSet (step x hm c) hnext ψ (retained d.frame) h g hg
      (Fin.cons a values) next:=
    (jointEndpointSet_retained_iff x hm c hnext φ ψ d.frame h g hg values a H HN old b).mpr hb
  have HK : d.retain.labels.length<n+1:=by rw [d.retain_length];exact hk
  exact joint_endpoint_at (step x hm c) hnext hn charge hdegree hcap d.retain HK
    (retained d.frame) h g d.frame_retain (by rw [d.retain_length];rfl) hg
    (by rw [d.retain_length];exact HG) z hz ψ hψ (Fin.cons a values) HN next b HB

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
