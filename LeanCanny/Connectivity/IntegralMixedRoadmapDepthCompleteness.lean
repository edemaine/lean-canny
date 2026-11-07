/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapGlobalSimulation
public import LeanCanny.Connectivity.IntegralMixedRoadmapCanonicalCriticalPoints
/-! # Native completeness by actual frozen-coordinate depth -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Connectivity LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedRoadmapGraph
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapAtomic.levels
  IntegralMixedRoadmapRetainedAppend.ownPoint IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentState IntegralMixedRoadmapRetainedAppend.parentValues
  canonicalPointAt pointAt

/-- The next-depth induction hypothesis simulates every actual path between
accepted representatives of the current frozen slice. -/
theorem depth_complete_step (candidate :List Bool) (k :ℕ) (hk :k<n (pairFst candidate)+3)
    (IH :DepthComplete hn ht ha hR0 candidate (k+1)):
    DepthComplete hn ht ha hR0 candidate k:=by
  intro first second hFirst hSecond hcFirst hcSecond hDepthFirst hDepthSecond hPath
  subst candidate
  have hd :IntegralMixedRoadmapAtomic.depth first<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 first:=by
    rw [hDepthFirst,IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 first]
    exact hk
  let p:=IntegralMixedRoadmapRetainedAppend.ownPoint hn ht ha hR0 first hFirst
  have HP:=(IntegralMixedRoadmapRetainedAppend.own_point_eligible hn ht ha hR0 first hFirst hd).1
  have HPointP :canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate first) first rfl p=
      pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate first) first hFirst rfl:=
    canonicalPointAt_ownPoint hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate first) first hFirst rfl
  have HImage:=canonical_slice_image hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate first)
    first hFirst hd rfl
  have HSecond:=hPath.target_mem
  rw [←HImage] at HSecond
  obtain ⟨q,HQ,HPointQ⟩:=HSecond
  have HDepth :IntegralMixedRoadmapAtomic.depth second=IntegralMixedRoadmapAtomic.depth first:=
    hDepthSecond.trans hDepthFirst.symm
  have Hpjoint:=canonical_height_mem_jointEndpointSet hn ht ha hR0 first hFirst hd
    first hFirst rfl rfl p HPointP HP
  have Hqjoint:=canonical_height_mem_jointEndpointSet hn ht ha hR0 first hFirst hd
    second hSecond hcSecond HDepth q HPointQ HQ
  have HGp:=canonical_child_partials hn ht ha hR0 first hFirst hd first hFirst rfl rfl p HPointP
  have HGq:=canonical_child_partials hn ht ha hR0 first hFirst hd second hSecond hcSecond HDepth q HPointQ
  have HCanonical:=(canonical_slice_joined_iff hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate first)
    first hFirst hd rfl p q).mpr (by simpa only [HPointP,HPointQ] using hPath)
  have HChild :DepthComplete hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate first)
      (IntegralMixedRoadmapAtomic.depth first+1):=by simpa only [hDepthFirst] using IH
  have HReach:=point_reachable_of_canonical_path hn ht ha hR0 first hFirst hd p q HP HQ
    Hpjoint Hqjoint HGp HGq HCanonical HChild
  have HNative:=Eq.mp (congrArg₂ (PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate first))
    HPointP HPointQ) HReach
  exact (point_reachable_iff_raw hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate first)
    first second hFirst hSecond rfl hcSecond).mp HNative

/-- Every legal depth is complete, by descending induction from the
terminal-fiber theorem. -/
theorem depth_complete (candidate :List Bool) (k :ℕ) (hk :k≤n (pairFst candidate)+3):
    DepthComplete hn ht ha hR0 candidate k:=by
  induction hk using Nat.decreasingInduction with
  | self => exact depth_complete_terminal hn ht ha hR0 candidate
  | of_succ k hk ih => exact depth_complete_step hn ht ha hR0 candidate k hk ih

/-- At depth zero the frozen slice is the original regular zero set. Both
endpoint histories remain independently accepted with their own full words. -/
theorem depth_zero_raw_reachable_iff_joined (candidate first second :List Bool)
    (hFirst :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 first)
    (hSecond :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 second)
    (hcFirst :IntegralMixedRoadmapAtomic.candidate first=candidate)
    (hcSecond :IntegralMixedRoadmapAtomic.candidate second=candidate)
    (hDepthFirst :IntegralMixedRoadmapAtomic.depth first=0)
    (hDepthSecond :IntegralMixedRoadmapAtomic.depth second=0):
    RawReachable hn ht ha hR0 candidate first second↔
      JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) candidate)
        (pointAt hn ht ha hR0 candidate first hFirst hcFirst)
        (pointAt hn ht ha hR0 candidate second hSecond hcSecond):=by
  constructor
  · exact raw_reachable_joined hn ht ha hR0 candidate first second
  · intro H
    have HZero :frozenSlice (n:=n) (t:=t) (R0:=R0) candidate
        (IntegralMixedRoadmapAtomic.depth first) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 first hFirst)=
        zeroSet (n:=n) (t:=t) (R0:=R0) candidate:=by
      simp [frozenSlice, hDepthFirst]
    exact depth_complete hn ht ha hR0 candidate 0 (by omega) first second hFirst hSecond
      hcFirst hcSecond hDepthFirst hDepthSecond (by simpa only [HZero] using H)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
