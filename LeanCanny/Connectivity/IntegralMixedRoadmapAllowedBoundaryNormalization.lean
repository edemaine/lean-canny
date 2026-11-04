/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FiniteSlabEndpointNormalization
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendEndpointCritical
/-! # Normalize every actual cut point to a same-fiber weak child-critical sample -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapAllowedBoundaryNormalization
open LeanCanny.Encoding LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open FiniteSlabEndpointPaths
open Set LeanCanny.Connectivity LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedFrozenFrame IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedFramedPhysicalIndex (arity enumerate)
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
noncomputable local instance allowedBoundaryNormalizationIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
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

local notation "heightMap"=>coarseProjection Q (line (Descriptor.frame d) h) V h

private theorem projection_physical (p :slice Q (coarse (line (d).frame h) h) V):
    heightMap p=p.val h:=
  line_projection (d).frame h ((d).free_normal h (IntegralMixedChronologicalSweepFrame.next_free d hk)) V p.val

private theorem boundary_representative (cutCount :ℕ) (cut :ℕ→ℝ)
    (origin :∀idx :Fin (cutCount+2),(∃endpoint :ParentEndpoint hn ht ha hR0 old hv hd,
      endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices) ∧ endpoint.value V=cut idx.val) ∨
      heightMap ⁻¹' {cut idx.val}=∅)
    (z :CutPoint heightMap cut cutCount):
    ∃q :slice Q (coarse (line (d).frame h) h) V,
      heightMap q=heightMap z.val ∧ JoinedIn (heightMap ⁻¹' {heightMap z.val}) z.val q ∧
      ∀i,i∉insert h (d).frame.frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
          (Int.castRingHom ℝ) q.val=0:=by
  obtain ⟨idx,hidx⟩:=z.property
  obtain ⟨endpoint,HAllowed,HValue⟩ :∃endpoint :ParentEndpoint hn ht ha hR0 old hv hd,
      endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices) ∧
      endpoint.value V=heightMap z.val:=by
    rcases origin idx with ⟨endpoint,HAllowed,HValue⟩|Hempty
    · exact ⟨endpoint,HAllowed,HValue.trans hidx.symm⟩
    · have HMem:z.val∈heightMap ⁻¹' {cut idx.val}:=hidx
      rw [Hempty] at HMem
      exact False.elim HMem
  have HSource:z.val.val∈slice Q (d).frame V:=by
    exact ((coarseLineHomeomorph Q (d).frame V h
      (IntegralMixedChronologicalSweepFrame.next_free d hk)).symm z.val).property
  obtain ⟨point,Hpath,Hslice,Hheight,Hgrad⟩:=exists_joined_allowed_endpoint_critical hn ht ha hR0 old hv hd
    endpoint HAllowed z.val.val HSource
    ((projection_physical hn ht ha hR0 old hv hd z.val).symm.trans HValue.symm)
  have Hpath' :JoinedIn (slice Q (d).frame V∩{y |y h=heightMap z.val}) z.val.val point:=by
    simpa only [HValue] using Hpath
  let q:slice Q (coarse (line (d).frame h) h) V:=
    coarseLineHomeomorph Q (d).frame V h (IntegralMixedChronologicalSweepFrame.next_free d hk) ⟨point,Hslice⟩
  have HProjection:heightMap q=heightMap z.val:=
    (projection_physical hn ht ha hR0 old hv hd q).trans (Hheight.trans HValue)
  have HShift:JoinedIn (shiftedSlice Q (line (d).frame h) V h (heightMap z.val)) z.val.val q.val:=by
    rw [line_slice Q (d).frame h (IntegralMixedChronologicalSweepFrame.next_free d hk) (d).free_normal]
    exact Hpath'
  have HFiber:JoinedIn (heightMap ⁻¹' {heightMap z.val}) z.val q:=
    (joined_fiber_iff Q (line (d).frame h) V h (Finset.mem_insert_self _ _) (heightMap z.val)
      z.val q rfl HProjection).mpr HShift
  exact ⟨q,HProjection,HFiber,Hgrad⟩

/-- All cut vertices, including previously noncritical intermediate points,
receive same-height weak child-critical representatives. Their actual fiber
paths map the ENTIRE finite closed-slab walk to those representatives. -/
theorem exists_allowed_critical_representatives (cutCount :ℕ) (cut :ℕ→ℝ)
    (origin :∀idx :Fin (cutCount+2),(∃endpoint :ParentEndpoint hn ht ha hR0 old hv hd,
      endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices) ∧ endpoint.value V=cut idx.val) ∨
      heightMap ⁻¹' {cut idx.val}=∅)
    {z w :CutPoint heightMap cut cutCount} (H :EndpointReach heightMap cut z w):
    ∃representative :CutPoint heightMap cut cutCount→CutPoint heightMap cut cutCount,
      (∀point,heightMap (representative point).val=heightMap point.val ∧
        JoinedIn (heightMap ⁻¹' {heightMap point.val}) point.val (representative point).val ∧
        ∀i,i∉insert h (d).frame.frozen→i≠g→
          (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
            (Int.castRingHom ℝ) (representative point).val.val=0) ∧
      EndpointReach heightMap cut (representative z) (representative w):=by
  have HA:=boundary_representative hn ht ha hR0 old hv hd cutCount cut origin
  choose point hheight hpath hgrad using HA
  let representative:CutPoint heightMap cut cutCount→CutPoint heightMap cut cutCount:=fun z=>
    ⟨point z,by obtain ⟨idx,hi⟩:=z.property;exact ⟨idx,(hheight z).trans hi⟩⟩
  have HHeight:∀z,heightMap (representative z).val=heightMap z.val:=hheight
  have HFiber:∀z,JoinedIn (heightMap ⁻¹' {heightMap z.val}) z.val (representative z).val:=hpath
  refine ⟨representative,fun z=>⟨HHeight z,HFiber z,hgrad z⟩,?_⟩
  exact endpointReach_map_fiber heightMap cut representative HHeight HFiber H

end LeanCanny.Connectivity.IntegralMixedRoadmapAllowedBoundaryNormalization
