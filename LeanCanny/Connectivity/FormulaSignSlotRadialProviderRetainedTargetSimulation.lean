/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderRetainedSweepSlabSimulation
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderAllowedBoundaryNormalization
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderCanonicalSweep
public import LeanCanny.Geometry.IntegralMixedMatchedFiniteSweep
public import LeanCanny.Geometry.IntegralMixedMatchedSlabAtomicPaths
/-! # Actual native graph simulation for a retained-target sweep -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints
open IntegralMixedRelativeCuts IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "E" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "r" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old E
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd E he
local notation "x" => FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd E he
local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd E he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd E he
local notation "V" => FormulaSignSlotRadialProviderRetainedAppend.parentValues old hv hd E he
local notation "phi" => FormulaSignSlotRadialProviderRetainedAppend.parentHom old hv hd E he
local notation "hm" => FormulaSignSlotRadialProviderRetainedAppend.parent_horizon old hv hd E he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd E he
local notation "hg" => FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd E he
local notation "h" => IntegralMixedChronologicalSweepFrame.next d hk
local notation "choices" => FormulaSignSlotRadialProviderRetainedAppend.levelChoices old hv hd E he
noncomputable local instance providerRetainedTargetSimulationIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.levelChoices

open FormulaSignSlotRadialProviderGraph FiniteSlabEndpointPaths Set

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
    (p q :Fin ((P).ambient r+1)→ℝ)
    (HP :p∈slice (Q r) (d).frame V) (HQ :q∈slice (Q r) (d).frame V)
    (HpJoint :p h∈jointEndpointSet x hm phi (d).frame h g hg V choices)
    (Hqh :q h=V targetRef)
    (HGp :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial ((Q r)).low ((Q r)).leading ((Q r)).degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (HJ :JoinedIn (slice (Q r) (d).frame V) p q)
    (IH :DepthComplete (FormulaSignSlotRadialProviderAtomic.provider old)
      (FormulaSignSlotRadialProviderAtomic.depth old+1)):
    ∃sample :Fin ((P).ambient r+1)→ℝ,
      sample∈slice (Q r) (d).frame V ∧ sample h=q h ∧
      JoinedIn (slice (Q r) (d).frame V∩{y |y h=q h}) sample q ∧
      (∀i,i∉insert h (d).frame.frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial ((Q r)).low ((Q r)).leading ((Q r)).degree)).eval₂
          (Int.castRingHom ℝ) sample=0) ∧
      PointReachable (FormulaSignSlotRadialProviderAtomic.provider old)
        (providerPoint old p)
        (providerPoint old sample):=by
  obtain ⟨W⟩:=exists_canonical_retained_sweep old hv hd targetRef
  have hh:=IntegralMixedChronologicalSweepFrame.next_free d hk
  let S:=slice (Q r) (coarse (line (d).frame h) h) V
  let heightMap :S→ℝ:=coarseProjection (Q r) (line (d).frame h) V h
  have HProjection (point :S):heightMap point=point.val h:=
    line_projection (d).frame h ((d).free_normal h hh) V point.val
  let u :S:=⟨p,by simpa only [S,coarse_line (d).frame h hh] using HP⟩
  let v :S:=⟨q,by simpa only [S,coarse_line (d).frame h hh] using HQ⟩
  have HUsed (point :CutPoint heightMap W.cut W.slabs):
      ∃endpoint :ParentEndpoint old hv hd,
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
      (coarseProjection_continuous (Q r) (line (d).frame h) V h) HStrict W.range_bound HSub
  obtain ⟨rep,HRep,_⟩:=FormulaSignSlotRadialProviderAllowedBoundaryNormalization.exists_allowed_critical_representatives
    old hv hd W.slabs W.cut W.origin HWalk
  have HSource (point :CutPoint heightMap W.cut W.slabs):
      point.val.val∈slice (Q r) (d).frame V:=by
    simpa only [S,coarse_line (d).frame h hh] using point.val.property
  have HRepHeight (point :CutPoint heightMap W.cut W.slabs):
      (rep point).val.val h=heightMap point.val:=
    (HProjection (rep point).val).symm.trans (HRep point).1
  let Reach (first second :CutPoint heightMap W.cut W.slabs):Prop:=
    PointReachable (FormulaSignSlotRadialProviderAtomic.provider old)
      (providerPoint old (rep first).val.val)
      (providerPoint old (rep second).val.val)
  have HRefl (point :CutPoint heightMap W.cut W.slabs):Reach point point:=by
    obtain ⟨endpoint,HAllowed,HValue⟩:=HUsed point
    exact point_reachable_of_endpoint_fiber old hv hd endpoint HAllowed
      (rep point).val.val (rep point).val.val (HSource (rep point)) (HSource (rep point))
      ((HRepHeight point).trans HValue.symm) ((HRepHeight point).trans HValue.symm)
      (HRep point).2.2 (HRep point).2.2
      (JoinedIn.refl ⟨HSource (rep point),(HRepHeight point).trans HValue.symm⟩) IH
  have HStep {first second :CutPoint heightMap W.cut W.slabs}
      (H :SlabStep heightMap W.cut first second):Reach first second:=by
    have HNorm:=slabStep_map_fiber heightMap W.cut rep (fun point=>(HRep point).1)
      (fun point=>(HRep point).2.1) H
    obtain ⟨idx,hfirst,hsecond,hpath⟩:=HNorm
    have HPath :JoinedIn (slice (Q r) (d).frame V∩{y |y h∈Icc (W.cut idx.val) (W.cut (idx.val+1))})
        (rep first).val.val (rep second).val.val:=by
      apply (hpath.map continuous_subtype_val.continuousOn).mono
      rintro y ⟨point,hpoint,rfl⟩
      refine ⟨by simpa only [S,coarse_line (d).frame h hh] using point.property,?_⟩
      change heightMap point∈Icc (W.cut idx.val) (W.cut (idx.val+1)) at hpoint
      rwa [HProjection] at hpoint
    exact point_reachable_of_retained_sweep_slab old hv hd targetRef W idx
      (rep first).val.val (rep second).val.val (HSource (rep first)) (HSource (rep second))
      (by rwa [HProjection] at hfirst) (by rwa [HProjection] at hsecond)
      (HRep first).2.2 (HRep second).2.2 HPath IH
  have HMiddle :Reach cp cq:=global_walk_simulation (SlabStep heightMap W.cut) Reach
    HRefl (fun H K=>PointReachable.trans H K) (fun H=>HStep H) HWalk
  have HAttach (point :CutPoint heightMap W.cut W.slabs)
      (HG :∀i,i∉insert h (d).frame.frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial ((Q r)).low ((Q r)).leading ((Q r)).degree)).eval₂
          (Int.castRingHom ℝ) point.val.val=0):
      PointReachable (FormulaSignSlotRadialProviderAtomic.provider old)
        (providerPoint old point.val.val)
        (providerPoint old (rep point).val.val):=by
    obtain ⟨endpoint,HAllowed,HValue⟩:=HUsed point
    apply point_reachable_of_endpoint_fiber old hv hd endpoint HAllowed
      point.val.val (rep point).val.val (HSource point) (HSource (rep point))
      ((HProjection point.val).symm.trans HValue.symm) ((HRepHeight point).trans HValue.symm)
      HG (HRep point).2.2
    · rw [HValue]
      simpa only [S,coarse_line (d).frame h hh] using
        global_fiber_path S heightMap (fun y=>y h) HProjection (heightMap point.val) (HRep point).2.1
    · exact IH
  have HLastHeight :(rep cq).val.val h=q h:=
    (HRepHeight cq).trans (HProjection v)
  have HLastPath :JoinedIn (slice (Q r) (d).frame V∩{y |y h=q h}) (rep cq).val.val q:=by
    have HPath:=global_fiber_path S heightMap (fun y=>y h) HProjection (heightMap cq.val) (HRep cq).2.1
    have HValue :heightMap cq.val=q h:=HProjection v
    rw [HValue] at HPath
    simpa only [S,coarse_line (d).frame h hh] using HPath.symm
  exact ⟨(rep cq).val.val,HSource (rep cq),HLastHeight,HLastPath,(HRep cq).2.2,
    PointReachable.trans (HAttach cp HGp) HMiddle⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
