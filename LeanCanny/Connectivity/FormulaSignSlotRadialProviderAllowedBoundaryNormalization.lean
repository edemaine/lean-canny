/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderEndpointCritical
public import LeanCanny.Connectivity.FiniteSlabEndpointNormalization
/-! # Normalize actual provider cut points to same-fiber weak critical samples -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderAllowedBoundaryNormalization
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Encoding
open LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open FiniteSlabEndpointPaths Set
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFrozenFrame
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
noncomputable local instance providerBoundaryNormalizationIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.levelChoices

local notation "heightMap"=>coarseProjection (Q r) (line (IntegralMixedChronologicalFrame.Descriptor.frame d) h) V h

private theorem projection_physical (p :slice (Q r) (coarse (line (d).frame h) h) V):
    heightMap p=p.val h:=
  line_projection (d).frame h ((d).free_normal h (IntegralMixedChronologicalSweepFrame.next_free d hk)) V p.val

private theorem boundary_representative (cutCount :ℕ) (cut :ℕ→ℝ)
    (origin :∀idx :Fin (cutCount+2),(∃endpoint :ParentEndpoint old hv hd,
      endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices) ∧ endpoint.value V=cut idx.val) ∨
      heightMap ⁻¹' {cut idx.val}=∅)
    (z :CutPoint heightMap cut cutCount):
    ∃q :slice (Q r) (coarse (line (d).frame h) h) V,
      heightMap q=heightMap z.val ∧ JoinedIn (heightMap ⁻¹' {heightMap z.val}) z.val q ∧
      ∀i,i∉insert h (d).frame.frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial ((Q r)).low ((Q r)).leading ((Q r)).degree)).eval₂
          (Int.castRingHom ℝ) q.val=0:=by
  obtain ⟨idx,hidx⟩:=z.property
  obtain ⟨endpoint,HAllowed,HValue⟩ :∃endpoint :ParentEndpoint old hv hd,
      endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices) ∧
      endpoint.value V=heightMap z.val:=by
    rcases origin idx with ⟨endpoint,HAllowed,HValue⟩|Hempty
    · exact ⟨endpoint,HAllowed,HValue.trans hidx.symm⟩
    · have HMem:z.val∈heightMap ⁻¹' {cut idx.val}:=hidx
      rw [Hempty] at HMem
      exact False.elim HMem
  have HSource:z.val.val∈slice (Q r) (d).frame V:=by
    exact ((coarseLineHomeomorph (Q r) (d).frame V h
      (IntegralMixedChronologicalSweepFrame.next_free d hk)).symm z.val).property
  obtain ⟨point,Hpath,Hslice,Hheight,Hgrad⟩:=exists_joined_allowed_endpoint_critical old hv hd
    endpoint HAllowed z.val.val HSource
    ((projection_physical old hv hd z.val).symm.trans HValue.symm)
  have Hpath' :JoinedIn (slice (Q r) (d).frame V∩{y |y h=heightMap z.val}) z.val.val point:=by
    simpa only [HValue] using Hpath
  let q:slice (Q r) (coarse (line (d).frame h) h) V:=
    coarseLineHomeomorph (Q r) (d).frame V h (IntegralMixedChronologicalSweepFrame.next_free d hk) ⟨point,Hslice⟩
  have HProjection:heightMap q=heightMap z.val:=
    (projection_physical old hv hd q).trans (Hheight.trans HValue)
  have HShift:JoinedIn (shiftedSlice (Q r) (line (d).frame h) V h (heightMap z.val)) z.val.val q.val:=by
    rw [line_slice (Q r) (d).frame h (IntegralMixedChronologicalSweepFrame.next_free d hk) (d).free_normal]
    exact Hpath'
  have HFiber:JoinedIn (heightMap ⁻¹' {heightMap z.val}) z.val q:=
    (joined_fiber_iff (Q r) (line (d).frame h) V h (Finset.mem_insert_self _ _) (heightMap z.val)
      z.val q rfl HProjection).mpr HShift
  exact ⟨q,HProjection,HFiber,Hgrad⟩

/-- All cut vertices, including previously noncritical intermediate points,
receive same-height weak child-critical representatives. Their actual fiber
paths map the ENTIRE finite closed-slab walk to those representatives. -/
theorem exists_allowed_critical_representatives (cutCount :ℕ) (cut :ℕ→ℝ)
    (origin :∀idx :Fin (cutCount+2),(∃endpoint :ParentEndpoint old hv hd,
      endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices) ∧ endpoint.value V=cut idx.val) ∨
      heightMap ⁻¹' {cut idx.val}=∅)
    {z w :CutPoint heightMap cut cutCount} (H :EndpointReach heightMap cut z w):
    ∃representative :CutPoint heightMap cut cutCount→CutPoint heightMap cut cutCount,
      (∀point,heightMap (representative point).val=heightMap point.val ∧
        JoinedIn (heightMap ⁻¹' {heightMap point.val}) point.val (representative point).val ∧
        ∀i,i∉insert h (d).frame.frozen→i≠g→
          (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial ((Q r)).low ((Q r)).leading ((Q r)).degree)).eval₂
            (Int.castRingHom ℝ) (representative point).val.val=0) ∧
      EndpointReach heightMap cut (representative z) (representative w):=by
  have HA:=boundary_representative old hv hd cutCount cut origin
  choose point hheight hpath hgrad using HA
  let representative:CutPoint heightMap cut cutCount→CutPoint heightMap cut cutCount:=fun z=>
    ⟨point z,by obtain ⟨idx,hi⟩:=z.property;exact ⟨idx,(hheight z).trans hi⟩⟩
  have HHeight:∀z,heightMap (representative z).val=heightMap z.val:=hheight
  have HFiber:∀z,JoinedIn (heightMap ⁻¹' {heightMap z.val}) z.val (representative z).val:=hpath
  refine ⟨representative,fun z=>⟨HHeight z,HFiber z,hgrad z⟩,?_⟩
  exact endpointReach_map_fiber heightMap cut representative HHeight HFiber H

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderAllowedBoundaryNormalization
