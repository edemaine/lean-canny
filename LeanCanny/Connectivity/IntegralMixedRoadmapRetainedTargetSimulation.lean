/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapAllowedBoundaryNormalization
public import LeanCanny.Connectivity.IntegralMixedRoadmapRetainedSweepSlabSimulation
public import LeanCanny.Connectivity.IntegralMixedRoadmapCanonicalRetainedSweep
public import LeanCanny.Geometry.IntegralMixedMatchedFiniteSweep
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendGeometryBudget
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCanonicalEndpoints
/-! # An accepted canonical parent supplies its actual finite matched sweep -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Connectivity LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedFrozenFrame IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "E"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old E
local notation "cs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd E he
local notation "ho"=>IntegralMixedRoadmapRetainedAppend.parent_room hn ht ha hR0 old hv hd E he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd E he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd E he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd E he
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd E he
local notation "Q"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c
local notation "hQ"=>IntegralMixedStaticRecordPrefix.cap Q (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)
local notation "phi"=>IntegralMixedRoadmapProperParent.hom hn ht ha hR0 old hv hd
local notation "hm"=>Nat.le_of_succ_le (IntegralMixedRoadmapProperParent.parent_room hn ht ha hR0 old hv hd)
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "h"=>IntegralMixedChronologicalSweepFrame.next d hk
local notation "choices"=>IntegralMixedRoadmapProperParent.choices hn ht ha hR0 old hv hd
noncomputable local instance retainedTargetSimulationIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapChain.metadata IntegralMixedRoadmapChain.rawStart
  IntegralMixedRoadmapRetainedAppend.start IntegralMixedRoadmapChain.depth
  IntegralMixedRoadmapChain.prefixCount IntegralMixedRoadmapChain.entry IntegralMixedRoadmapChain.frozen
  IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapRetainedAppend.parentTuple
  IntegralMixedRoadmapRetainedAppend.parentValues IntegralMixedExceptionalBounds.auxiliaryCap
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedFramedRawHeight.rootCeiling
  IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedFramedHistoryScript.run IntegralMixedHistory.reframe
  IntegralMixedFramedHistoryFamilyBits.initial IntegralMixedRoadmapProperParent.hom
  IntegralMixedRoadmapProperParent.choices IntegralMixedRoadmapRetainedAppend.parentState

open IntegralMixedRoadmapGraph FiniteSlabEndpointPaths Set

private theorem global_walk_simulation {α :Type} (stepRel R :α→α→Prop)
    (hrefl :∀v,R v v) (htrans :∀{u v w},R u v→R v w→R u w)
    (hstep :∀{u v},stepRel u v→R u v) {u v :α} (H :Relation.ReflTransGen stepRel u v):R u v:=by
  induction H with
  | refl=>exact hrefl _
  | tail _ edgeProof ih=>exact htrans ih (hstep edgeProof)

private theorem global_fiber_path {X :Type} [TopologicalSpace X] (S :Set X)
    (f :S→ℝ) (height :X→ℝ) (HF :∀y,f y=height y.val)
    (value :ℝ) {u v :S} (H :JoinedIn (f ⁻¹' {value}) u v):
    JoinedIn (S∩{y |height y=value}) u.val v.val:=by
  apply (H.map continuous_subtype_val.continuousOn).mono
  rintro y ⟨point,hpoint,rfl⟩
  exact ⟨point.property,(HF point).symm.trans hpoint⟩

/-- The whole canonical frozen-slice path is simulated by actual native
paths, with only the next-depth completeness statement used recursively. -/
theorem exists_reachable_critical_in_target_fiber
    (targetRef :Fin (cs).length)
    (p q :Fin ((P).ambient c+1)→ℝ)
    (HP :p∈slice Q (d).frame V) (HQ :q∈slice Q (d).frame V)
    (HpJoint :p h∈jointEndpointSet x hm phi (d).frame h g hg V choices)
    (Hqh :q h=V targetRef)
    (HGp :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (HJ :JoinedIn (slice Q (d).frame V) p q)
    (IH :DepthComplete hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (IntegralMixedRoadmapAtomic.depth old+1)):
    ∃sample :Fin ((P).ambient c+1)→ℝ,
      sample∈slice Q (d).frame V ∧ sample h=q h ∧
      JoinedIn (slice Q (d).frame V∩{y |y h=q h}) sample q ∧
      (∀i,i∉insert h (d).frame.frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
          (Int.castRingHom ℝ) sample=0) ∧
      PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
        (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p)
        (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl sample):=by
  obtain ⟨W⟩:=exists_canonical_retained_sweep hn ht ha hR0 old hv hd targetRef
  have hh:=IntegralMixedChronologicalSweepFrame.next_free d hk
  let S:=slice Q (coarse (line (d).frame h) h) V
  let heightMap :S→ℝ:=coarseProjection Q (line (d).frame h) V h
  have HProjection (point :S):heightMap point=point.val h:=
    line_projection (d).frame h ((d).free_normal h hh) V point.val
  let u :S:=⟨p,by simpa only [S,coarse_line (d).frame h hh] using HP⟩
  let v :S:=⟨q,by simpa only [S,coarse_line (d).frame h hh] using HQ⟩
  have HUsed (point :CutPoint heightMap W.cut W.slabs):
      ∃endpoint :ParentEndpoint hn ht ha hR0 old hv hd,
        endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices) ∧
        endpoint.value V=heightMap point.val:=by
    obtain ⟨idx,hidx⟩:=point.property
    rcases W.origin idx with ⟨endpoint,HAllowed,HValue⟩|HEmpty
    · exact ⟨endpoint,HAllowed,HValue.trans hidx.symm⟩
    · have HMem :point.val∈heightMap ⁻¹' {W.cut idx.val}:=hidx
      rw [HEmpty] at HMem
      exact False.elim HMem
  obtain ⟨ip,hip⟩:=W.includes_bad (p h) HpJoint
  obtain ⟨iq,hiq⟩:=W.includes_target
  let cp :CutPoint heightMap W.cut W.slabs:=⟨u,ip,(HProjection u).trans hip.symm⟩
  let cq :CutPoint heightMap W.cut W.slabs:=⟨v,iq,(HProjection v).trans (hiq.trans Hqh.symm).symm⟩
  have HSub :JoinedIn (Set.univ :Set S) u v:=by
    apply joinedIn_univ.mpr
    apply (joinedIn_iff_joined u.property v.property).mp
    simpa only [S,coarse_line (d).frame h hh] using HJ
  have HStrict :StrictMonoOn W.cut (Set.Icc 0 (W.slabs+1)):=by
    intro i hi j hj hij
    have HI :i≤W.slabs+1:=hi.2
    have HJ :j≤W.slabs+1:=hj.2
    exact W.strict (a:=⟨i,by omega⟩) (b:=⟨j,by omega⟩) hij
  let :∀i,Finite (W.Index i):=W.finite_index
  have HWalk :EndpointReach heightMap W.cut cp cq:=
    endpointReach_of_joinedIn heightMap W.cut W.slabCover
      (coarseProjection_continuous Q (line (d).frame h) V h) HStrict W.range_bound HSub
  obtain ⟨rep,HRep,_⟩:=IntegralMixedRoadmapAllowedBoundaryNormalization.exists_allowed_critical_representatives
    hn ht ha hR0 old hv hd W.slabs W.cut W.origin HWalk
  have HSource (point :CutPoint heightMap W.cut W.slabs):
      point.val.val∈slice Q (d).frame V:=by
    simpa only [S,coarse_line (d).frame h hh] using point.val.property
  have HRepHeight (point :CutPoint heightMap W.cut W.slabs):
      (rep point).val.val h=heightMap point.val:=
    (HProjection (rep point).val).symm.trans (HRep point).1
  let Reach (first second :CutPoint heightMap W.cut W.slabs):Prop:=
    PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl (rep first).val.val)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl (rep second).val.val)
  have HRefl (point :CutPoint heightMap W.cut W.slabs):Reach point point:=by
    obtain ⟨endpoint,HAllowed,HValue⟩:=HUsed point
    exact point_reachable_of_endpoint_fiber hn ht ha hR0 old hv hd endpoint HAllowed
      (rep point).val.val (rep point).val.val (HSource (rep point)) (HSource (rep point))
      ((HRepHeight point).trans HValue.symm) ((HRepHeight point).trans HValue.symm)
      (HRep point).2.2 (HRep point).2.2
      (JoinedIn.refl ⟨HSource (rep point),(HRepHeight point).trans HValue.symm⟩) IH
  have HStep {first second :CutPoint heightMap W.cut W.slabs}
      (H :SlabStep heightMap W.cut first second):Reach first second:=by
    have HNorm:=slabStep_map_fiber heightMap W.cut rep (fun point=>(HRep point).1)
      (fun point=>(HRep point).2.1) H
    obtain ⟨idx,hfirst,hsecond,hpath⟩:=HNorm
    have HPath :JoinedIn (slice Q (d).frame V∩{y |y h∈Icc (W.cut idx.val) (W.cut (idx.val+1))})
        (rep first).val.val (rep second).val.val:=by
      apply (hpath.map continuous_subtype_val.continuousOn).mono
      rintro y ⟨point,hpoint,rfl⟩
      refine ⟨by simpa only [S,coarse_line (d).frame h hh] using point.property,?_⟩
      change heightMap point∈Icc (W.cut idx.val) (W.cut (idx.val+1)) at hpoint
      rwa [HProjection] at hpoint
    exact point_reachable_of_retained_sweep_slab hn ht ha hR0 old hv hd targetRef W idx
      (rep first).val.val (rep second).val.val (HSource (rep first)) (HSource (rep second))
      (by rwa [HProjection] at hfirst) (by rwa [HProjection] at hsecond)
      (HRep first).2.2 (HRep second).2.2 HPath IH
  have HMiddle :Reach cp cq:=global_walk_simulation (SlabStep heightMap W.cut) Reach
    HRefl (fun H K=>PointReachable.trans hn ht ha hR0 H K) (fun H=>HStep H) HWalk
  have HAttach (point :CutPoint heightMap W.cut W.slabs)
      (HG :∀i,i∉insert h (d).frame.frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
          (Int.castRingHom ℝ) point.val.val=0):
      PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
        (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl point.val.val)
        (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl (rep point).val.val):=by
    obtain ⟨endpoint,HAllowed,HValue⟩:=HUsed point
    apply point_reachable_of_endpoint_fiber hn ht ha hR0 old hv hd endpoint HAllowed
      point.val.val (rep point).val.val (HSource point) (HSource (rep point))
      ((HProjection point.val).symm.trans HValue.symm) ((HRepHeight point).trans HValue.symm)
      HG (HRep point).2.2
    · rw [HValue]
      simpa only [S,coarse_line (d).frame h hh] using
        global_fiber_path S heightMap (fun y=>y h) HProjection (heightMap point.val) (HRep point).2.1
    · exact IH
  have HLastHeight :(rep cq).val.val h=q h:=
    (HRepHeight cq).trans (HProjection v)
  have HLastPath :JoinedIn (slice Q (d).frame V∩{y |y h=q h}) (rep cq).val.val q:=by
    have HPath:=global_fiber_path S heightMap (fun y=>y h) HProjection (heightMap cq.val) (HRep cq).2.1
    have HValue :heightMap cq.val=q h:=HProjection v
    rw [HValue] at HPath
    simpa only [S,coarse_line (d).frame h hh] using HPath.symm
  exact ⟨(rep cq).val.val,HSource (rep cq),HLastHeight,HLastPath,(HRep cq).2.2,
    PointReachable.trans hn ht ha hR0 (HAttach cp HGp) HMiddle⟩

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
