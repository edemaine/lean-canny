/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendGeometryBudget
public import LeanCanny.Geometry.IntegralMixedOptionalEndpointCriticalPaths
/-! # An arbitrary genuine cut-fiber point attaches to a child-critical sample -/
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
noncomputable local instance properAppendBoundaryCriticalIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
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

/-- Starting from an accepted old history, any point of a genuine fresh cut
fiber is joined INSIDE that fiber to a point satisfying the child equations.
No parent hom, optional pair, native word or supplied gradient is an input. -/
theorem exists_joined_boundary_critical (value :ℝ)
    (HAllowed :(Endpoint.fresh (m:=(cs).length) value).Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (p :Fin ((P).ambient c+1)→ℝ) (HSp :p∈slice Q (d).frame V) (Hhp :p h=value):
    ∃q :Fin ((P).ambient c+1)→ℝ,JoinedIn (slice Q (d).frame V∩{y | y h=value}) p q ∧
      q∈slice Q (d).frame V ∧ q h=value ∧
      ∀i,i∉insert h (d).frame.frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
          (Int.castRingHom ℝ) q=0:=by
  obtain ⟨R,_⟩:=IntegralMixedRoadmapProperParent.exists_guarded_pair hn ht ha hR0 old hv hd
    (.fresh value) (.fresh value) HAllowed HAllowed
  have HDegree :(Q).degree=BoundedZeroSource.powerDegree
      (t (IntegralMixedAuxiliaryMarkedIntegerSource.original c)).toData.size:=
    IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) c
  have HP:IsProperMap (fun y :Fin ((P).ambient c+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree).eval₂ (Int.castRingHom ℝ) y):=by
    rw [IntegralMixedOriginalRegularSource.spatial_source]
    exact regular_source_proper (BoundedRegularLowCoefficient.readers n t R0)
      (IntegralMixedAuxiliaryMarkedIntegerSource.original c)
  have HRoom :(cs).length+R.result.commands.length+((P).ambient c-(d).frame.frozen.card)≤(P).cap c+2:=by
    have HC:=R.result.count
    have HH:=canonical_level_horizon hn ht ha hR0 old hv hd
    rw [(d).frozen_card]
    omega
  exact R.result.exists_joined_endpoint_critical h
    (IntegralMixedChronologicalSweepFrame.next_free d hk) (d).frozen_card.symm g hg
    _ HDegree HP HRoom false p HSp Hhp

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
