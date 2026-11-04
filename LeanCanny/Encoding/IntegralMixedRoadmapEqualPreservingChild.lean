/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapEqualAppendGeometry
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLocalFields
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendGeometryBudget
public import LeanCanny.Geometry.IntegralMixedOptionalEndpointCriticalPaths
/-! # Retained or fresh endpoint fibers admit child-critical samples -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
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
local notation "z"=>IntegralMixedRoadmapRetainedAppend.parentTuple hn ht ha hR0 old hv hd E he
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd E he
local notation "Q"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c
local notation "hQ"=>IntegralMixedStaticRecordPrefix.cap Q (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)
local notation "phi"=>IntegralMixedRoadmapProperParent.hom hn ht ha hR0 old hv hd
local notation "hm"=>Nat.le_of_succ_le (IntegralMixedRoadmapProperParent.parent_room hn ht ha hR0 old hv hd)
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "h"=>IntegralMixedChronologicalSweepFrame.next d hk
local notation "choices"=>IntegralMixedRoadmapProperParent.choices hn ht ha hR0 old hv hd
noncomputable local instance preservingEqualChildIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
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

/-- A weak critical point on an allowed endpoint fiber has an accepted child
that preserves every earlier chronological field at its own new root. -/
theorem exists_equal_preserving_child (endpoint :ParentEndpoint hn ht ha hR0 old hv hd)
    (HAllowed :endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (p :Fin ((P).ambient c+1)→ℝ) (HS :p∈slice Q (d).frame V)
    (Hh :p h=endpoint.value V)
    (HG :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0):
    ∃child,∃hChild :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 child,
      IntegralMixedRoadmapAtomic.candidate child=IntegralMixedRoadmapAtomic.candidate old ∧
      IntegralMixedRoadmapAtomic.depth child=IntegralMixedRoadmapAtomic.depth old+1 ∧
      HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 child hChild) p ∧
      ∀b,b<beginBirth hn ht ha hR0 old→
        IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 child hChild b=
          IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 old hv b:=by
  obtain ⟨R,HE⟩:=exists_equal_geometric_level hn ht ha hR0 old hv hd endpoint endpoint
    HAllowed HAllowed rfl p HS Hh HG
  obtain ⟨u,hu,N,hOld⟩:=HE false
  obtain ⟨p0,W,hChild,hPoint,_⟩:=exists_accepted_receipt hn ht ha hR0 old hv hd
    endpoint endpoint R false u hu p p N hOld
  refine ⟨packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old
    R.leftSpec R.rightSpec false W.word,hChild,candidate_packet _ _ _ _ _ _,
    depth_packet _ _ _ _ _ _,hPoint,?_⟩
  exact W.original_old_fields hn ht ha hR0 old hv hd endpoint endpoint R false hChild hOld

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
