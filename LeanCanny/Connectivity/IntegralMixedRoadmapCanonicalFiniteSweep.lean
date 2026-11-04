/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
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
noncomputable local instance canonicalFiniteSweepIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
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

/-- The converted choices are the actual supplied canonical choices, and their
bad set is exactly the canonical ordinary-bad/real-critical endpoint set. -/
theorem canonical_sweep_badset :
    sweepBadReal x hm phi (d).frame h g hg V
      (prefixInputChoices x hm (d).frame h g hg
        (IntegralMixedChronologicalSweepFrame.prefix_frozen d hk) phi choices)=
      jointEndpointSet x hm phi (d).frame h g hg V choices:=
  prefixInputChoices_badset x hm (d).frame h g hg
    (IntegralMixedChronologicalSweepFrame.prefix_frozen d hk) phi V choices

/-- Original syntax and an accepted old node construct the entire finite
matched sweep. Actual states, homs, tuples, covers and room are internal. -/
theorem exists_canonical_matched_finite_sweep :
    Nonempty (MatchedFiniteSweep x hm phi (d).frame h g hg V
      (prefixInputChoices x hm (d).frame h g hg
        (IntegralMixedChronologicalSweepFrame.prefix_frozen d hk) phi choices)):=by
  have HRoom :(cs).length+2+((P).ambient c-(d).frame.frozen.card)≤(P).cap c+2:=by
    have HB:=canonical_level_horizon hn ht ha hR0 old hv hd
    rw [(d).frozen_card]
    omega
  have HProper :IsProperMap (fun y :Fin ((P).ambient c+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree).eval₂
        (Int.castRingHom ℝ) y):=
    regular_source_proper (BoundedRegularLowCoefficient.readers (IntegralMixedAuxiliaryMarkedIntegerSource.number n)
      (t∘IntegralMixedAuxiliaryMarkedIntegerSource.original) (radius R0)) c
  obtain ⟨_,HS⟩:=exists_matched_finite_sweep x hm
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha c)
    (t (IntegralMixedAuxiliaryMarkedIntegerSource.original c)).toData.size
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) c)
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)
    (d).frame (d).free_normal (d).atomic (d).prefix_frozen h
    (IntegralMixedChronologicalSweepFrame.next_free d hk) (d).frozen_card.symm g hg
    (IntegralMixedRoadmapRetainedAppend.parentTuple hn ht ha hR0 old hv hd E he)
    (IntegralMixedRoadmapRetainedAppend.parent_roots hn ht ha hR0 old hv hd E he)
    phi (IntegralMixedRoadmapProperParent.hom_generators hn ht ha hR0 old hv hd)
    V (IntegralMixedRoadmapProperParent.hom_values hn ht ha hR0 old hv hd) choices HRoom HProper
  exact HS

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
