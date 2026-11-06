/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderRetainedTargetSimulation
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphDepthCompleteness
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperEqualPreservingChild
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
noncomputable local instance providerRetainedTargetChildIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.levelChoices

open FormulaSignSlotRadialProviderGraph FiniteSlabEndpointPaths Set

/-- A genuine path toward a retained height produces a reachable accepted child,
retains every old field, and leaves the target in the actual child component. -/
theorem exists_child_toward_target (targetRef :Fin (cs).length)
    (q :Fin ((P).ambient r+1)→ℝ) (Hqh :q h=V targetRef)
    (HPath :JoinedIn (slice (Q r) (d).frame V)
      (FormulaSignSlotRadialProviderRetainedAppend.ownPoint old hv) q):
    ∃child,∃hChild:FormulaSignSlotRadialProviderAtomic.Valid child,
      ∃hc:FormulaSignSlotRadialProviderAtomic.provider child=FormulaSignSlotRadialProviderAtomic.provider old,
        FormulaSignSlotRadialProviderAtomic.depth child=FormulaSignSlotRadialProviderAtomic.depth old+1 ∧
        RawReachable (FormulaSignSlotRadialProviderAtomic.provider old) old child ∧
        (∀b,b<beginBirth old→FormulaSignSlotRadialProviderAtomic.field child hChild b=
          FormulaSignSlotRadialProviderAtomic.field old hv b) ∧
        JoinedIn (frozenSlice (FormulaSignSlotRadialProviderAtomic.provider old)
          (FormulaSignSlotRadialProviderAtomic.depth child) (FormulaSignSlotRadialProviderAtomic.levels child hChild))
          (pointAt (FormulaSignSlotRadialProviderAtomic.provider old) child hChild hc) (providerPoint old q):=by
  let p:=FormulaSignSlotRadialProviderRetainedAppend.ownPoint old hv
  have HP:=(FormulaSignSlotRadialProviderRetainedAppend.own_point_eligible old hv hd).1
  have HPointP:providerPoint old p=pointAt (FormulaSignSlotRadialProviderAtomic.provider old) old hv rfl:=
    eq_of_heq ((providerPoint_heq old p).trans
      ((FormulaSignSlotRadialProviderRetainedAppend.ownPoint_heq old hv).trans
        (native_pointAt_heq _ old hv rfl)))
  have HpJoint:=canonical_point_height_mem_jointEndpointSet old hv hd old hv rfl rfl p HPointP HP
  have HGp:=canonical_point_child_partials old hv hd old hv rfl rfl p HPointP
  have HDim:FormulaSignSlotRadialProviderAtomic.dimension old=
      FormulaSignSlotRadialProviderMarkedGeometry.number (FormulaSignSlotRadialProviderAtomic.provider old)+3:=
    FormulaSignSlotRadialProviderAtomic.dimension_provider old
  have IH:=depth_complete (FormulaSignSlotRadialProviderAtomic.provider old)
    (FormulaSignSlotRadialProviderAtomic.depth old+1) (by omega)
  obtain ⟨sample,HS,Hsh,HFiber,HG,HReach⟩:=exists_reachable_critical_in_target_fiber old hv hd
    targetRef p q HP HPath.target_mem HpJoint Hqh HGp HPath IH
  obtain ⟨child,hChild,hc,hdepth,HPoint,hFields⟩:=exists_equal_preserving_child old hv hd
    (.retained targetRef) True.intro sample HS (Hsh.trans Hqh) HG
  have HSample:=providerPoint_eq_pointAt_of_native_heq old child hChild hc sample HPoint
  have HNative:PointReachable (FormulaSignSlotRadialProviderAtomic.provider old)
      (pointAt (FormulaSignSlotRadialProviderAtomic.provider old) old hv rfl)
      (pointAt (FormulaSignSlotRadialProviderAtomic.provider old) child hChild hc):=by
    simpa only [HPointP,HSample] using HReach
  have HRaw:=(point_reachable_iff_raw _ old child hv hChild rfl hc).mp HNative
  let coord:=childCoordinate (FormulaSignSlotRadialProviderAtomic.provider old) old hv rfl
  have Hcoord:Fin.cast (parent_point_dimension old).symm coord=h:=by
    apply Fin.ext
    simp only [Fin.val_cast,coord,childCoordinate_val,IntegralMixedChronologicalSweepFrame.next]
    exact (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd E he).symm
  have HOld:pointAt (FormulaSignSlotRadialProviderAtomic.provider old) child hChild hc∈
      frozenSlice (FormulaSignSlotRadialProviderAtomic.provider old) (FormulaSignSlotRadialProviderAtomic.depth old)
        (FormulaSignSlotRadialProviderAtomic.levels old hv):=by
    rw [←HSample]
    exact (providerPoint_slice_iff old hv hd sample).mpr HS
  have Hheight:pointAt (FormulaSignSlotRadialProviderAtomic.provider old) child hChild hc coord=q h:=by
    rw [←HSample]
    change sample (Fin.cast _ coord)=q h
    rw [Hcoord]
    exact Hsh
  have HSlice:=child_frozenSlice_eq (FormulaSignSlotRadialProviderAtomic.provider old) old child hv hChild
    rfl hc hdepth HOld (q h) Hheight
  refine ⟨child,hChild,hc,hdepth,HRaw,?_,?_⟩
  · intro b hb
    exact hFields b (hb.trans_eq (begin_eq_start old))
  · rw [HSlice,←HSample]
    apply (HFiber.map (providerPoint_continuous old).continuousOn).mono
    rintro _ ⟨point,Hpoint,rfl⟩
    refine ⟨(providerPoint_slice_iff old hv hd point).mpr Hpoint.1,?_⟩
    change point (Fin.cast _ coord)=q h
    rw [Hcoord]
    exact Hpoint.2

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
