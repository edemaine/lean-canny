/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapRetainedTargetSimulation
public import LeanCanny.Connectivity.IntegralMixedRoadmapDepthCompleteness
public import LeanCanny.Encoding.IntegralMixedRoadmapEqualPreservingChild
/-! # A retained target gives an actual reachable child with every old field preserved -/
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
noncomputable local instance retainedTargetChildIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
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

open IntegralMixedRoadmapGraph
attribute [local irreducible] canonicalPointAt pointAt IntegralMixedRoadmapRetainedAppend.ownPoint

/-- A genuine old-slice path to the retained target yields a fresh accepted
child. All old chronological fields survive, and the target lies in the child's
actual path component. No marked-target or replay premise is needed. -/
theorem exists_child_toward_target (targetRef :Fin (cs).length)
    (q :Fin ((P).ambient c+1)→ℝ) (Hqh :q h=V targetRef)
    (HPath :JoinedIn (slice Q (d).frame V)
      (IntegralMixedRoadmapRetainedAppend.ownPoint hn ht ha hR0 old hv) q):
    ∃child,∃hChild :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 child,
      ∃hcCandidate :IntegralMixedRoadmapAtomic.candidate child=IntegralMixedRoadmapAtomic.candidate old,
        IntegralMixedRoadmapAtomic.depth child=IntegralMixedRoadmapAtomic.depth old+1 ∧
        RawReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old child ∧
        (∀b,b<beginBirth hn ht ha hR0 old→
          IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 child hChild b=
            IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 old hv b) ∧
        JoinedIn (frozenSlice (n:=n) (t:=t) (R0:=R0) (IntegralMixedRoadmapAtomic.candidate old)
          (IntegralMixedRoadmapAtomic.depth child) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 child hChild))
          (pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) child hChild hcCandidate)
          (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl q):=by
  let p:=IntegralMixedRoadmapRetainedAppend.ownPoint hn ht ha hR0 old hv
  have HP:=(IntegralMixedRoadmapRetainedAppend.own_point_eligible hn ht ha hR0 old hv hd).1
  have HPointP :canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p=
      pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old hv rfl:=
    canonicalPointAt_ownPoint hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old hv rfl
  have HpJoint:=canonical_height_mem_jointEndpointSet hn ht ha hR0 old hv hd old hv rfl rfl p HPointP HP
  have HGp:=canonical_child_partials hn ht ha hR0 old hv hd old hv rfl rfl p HPointP
  have HDim :IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old=
      n (pairFst (IntegralMixedRoadmapAtomic.candidate old))+3:=
    IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 old
  have IH:=depth_complete hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
    (IntegralMixedRoadmapAtomic.depth old+1) (by omega)
  obtain ⟨sample,HS,Hsh,HFiber,HG,HReach⟩:=exists_reachable_critical_in_target_fiber hn ht ha hR0 old hv hd
    targetRef p q HP HPath.target_mem HpJoint Hqh HGp HPath IH
  obtain ⟨child,hChild,hc,hdepth,HPoint,hFields⟩:=exists_equal_preserving_child hn ht ha hR0 old hv hd
    (.retained targetRef) True.intro sample HS (Hsh.trans Hqh) HG
  have HSample:=pointAt_eq_canonical_of_point_heq hn ht ha hR0 old child hChild hc sample HPoint
  have HNative:=Eq.mp (congrArg₂ (PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old))
    HPointP HSample.symm) HReach
  have HRaw:=(point_reachable_iff_raw hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
    old child hv hChild rfl hc).mp HNative
  let coord:=childCoordinate hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old hv rfl
  have Hcoord :Fin.cast (congrArg (·+1)
      (canonical_ambient_eq hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl)).symm coord=h:=by
    apply Fin.ext
    simp only [Fin.val_cast,coord,childCoordinate_val]
    exact (IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd E he).symm
  have HOld :pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) child hChild hc∈
      frozenSlice (n:=n) (t:=t) (R0:=R0) (IntegralMixedRoadmapAtomic.candidate old)
        (IntegralMixedRoadmapAtomic.depth old) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv):=by
    rw [HSample]
    exact (canonical_slice_iff_original hn ht ha hR0 _ old hv hd rfl sample).mp HS
  have Hheight :pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) child hChild hc coord=q h:=by
    rw [HSample]
    unfold canonicalPointAt
    rw [Hcoord]
    exact Hsh
  have HSlice:=child_frozenSlice_eq hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old child hv hChild
    rfl hc hdepth HOld (q h) Hheight
  refine ⟨child,hChild,hc,hdepth,HRaw,hFields,?_⟩
  rw [HSlice,HSample]
  apply (HFiber.map (canonicalPointAt_continuous hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate old) old rfl).continuousOn).mono
  rintro y ⟨point,Hpoint,rfl⟩
  refine ⟨(canonical_slice_iff_original hn ht ha hR0 _ old hv hd rfl point).mp Hpoint.1,?_⟩
  unfold canonicalPointAt
  change point (Fin.cast _ coord)=q h
  rw [Hcoord]
  exact Hpoint.2

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
