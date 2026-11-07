/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGlobalSimulation
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphCriticalEndpoints
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphProperGeometry
/-! # Actual native provider completeness by the number of unfrozen coordinates -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "provider" => FormulaSignSlotRadialProviderAtomic.provider
local notation "depth" => FormulaSignSlotRadialProviderAtomic.depth
local notation "dim" => FormulaSignSlotRadialProviderAtomic.dimension
local notation "num" => FormulaSignSlotRadialProviderMarkedGeometry.number
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderAtomic.point FormulaSignSlotRadialProviderAtomic.levels
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentValues

theorem depth_complete_step (c : List Bool) (k : ℕ) (hk : k<num c+3)
    (IH : DepthComplete c (k+1)) : DepthComplete c k := by
  intro first second hFirst hSecond hcFirst hcSecond hDepthFirst hDepthSecond hPath
  subst c
  subst k
  have hd : depth first<dim first := by
    have HD : dim first=num (provider first)+3 := FormulaSignSlotRadialProviderAtomic.dimension_provider first
    omega
  let p := parentPoint first (pointAt (provider first) first hFirst rfl)
  let q := parentPoint first (pointAt (provider first) second hSecond hcSecond)
  have HP := (parent_slice_iff first hFirst hd _).mpr hPath.source_mem
  have HQ := (parent_slice_iff first hFirst hd _).mpr hPath.target_mem
  have HEp : providerPoint first p=pointAt (provider first) first hFirst rfl := providerPoint_parentPoint first _
  have HEq : providerPoint first q=pointAt (provider first) second hSecond hcSecond := providerPoint_parentPoint first _
  have Hpjoint := canonical_point_height_mem_jointEndpointSet first hFirst hd first hFirst rfl rfl p HEp HP
  have Hqjoint := canonical_point_height_mem_jointEndpointSet first hFirst hd second hSecond hcSecond hDepthSecond q HEq HQ
  have HGp := canonical_point_child_partials first hFirst hd first hFirst rfl rfl p HEp
  have HGq := canonical_point_child_partials first hFirst hd second hSecond hcSecond hDepthSecond q HEq
  have HCanonical := parent_joinedIn first hFirst hd _ _ hPath
  have HReach := FormulaSignSlotRadialProviderProperAppend.point_reachable_of_canonical_path
    first hFirst hd p q HP HQ Hpjoint Hqjoint HGp HGq HCanonical IH
  exact (point_reachable_iff_raw _ first second hFirst hSecond rfl hcSecond).mp (by
    simpa only [HEp,HEq] using HReach)

theorem depth_complete (c : List Bool) (k : ℕ) (hk : k≤num c+3) : DepthComplete c k := by
  induction hk using Nat.decreasingInduction with
  | self => exact depth_complete_terminal c
  | of_succ k hk ih => exact depth_complete_step c k hk ih

theorem depth_zero_raw_reachable_iff_joined (c first second : List Bool) (hFirst : A first) (hSecond : A second)
    (hcFirst : provider first=c) (hcSecond : provider second=c)
    (hDepthFirst : depth first=0) (hDepthSecond : depth second=0) :
    RawReachable c first second ↔ JoinedIn (FormulaSignSlotRadialProviderMarkedGeometry.zeroSet c)
      (pointAt c first hFirst hcFirst) (pointAt c second hSecond hcSecond) := by
  constructor
  · exact raw_reachable_joined c first second
  · intro H
    have HZero : frozenSlice c 0 (FormulaSignSlotRadialProviderAtomic.levels first hFirst)=
        FormulaSignSlotRadialProviderMarkedGeometry.zeroSet c := by
      simp [frozenSlice]
    exact depth_complete c 0 (by omega) first second hFirst hSecond hcFirst hcSecond hDepthFirst hDepthSecond
      (by simpa only [HZero] using H)

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
