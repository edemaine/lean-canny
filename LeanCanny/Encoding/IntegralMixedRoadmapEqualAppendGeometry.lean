/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendGeometryBudget
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPhysical
public import LeanCanny.Geometry.IntegralMixedChronologicalGuardedEqualLevel
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendSampledExtension
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPastValues
/-! # An actual equal-height boundary fiber supplies accepted child histories -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Connectivity LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
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
noncomputable local instance equalAppendGeometryIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
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

private theorem equal_old_raw_from_typed (u :ℕ→ℝ)
    (H :∀idx :Index (Fin 0) cs,u (enumerate cs idx).val=z idx):
    ∀idx,idx<arity cs→u idx=oldNatural hn ht ha hR0 old hv idx:=by
  intro idx hi
  let typed:Index (Fin 0) cs:=(enumerate cs).symm ⟨idx,hi⟩
  have HE :(enumerate cs typed).val=idx:=by
    exact congrArg Fin.val ((enumerate cs).apply_symm_apply ⟨idx,hi⟩)
  have HZ :z typed=oldNatural hn ht ha hR0 old hv idx:=by
    unfold IntegralMixedRoadmapRetainedAppend.parentTuple
    rw [HE]
  exact (congrArg u HE).symm.trans ((H typed).trans HZ)

variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
local notation "a"=>left.value V
local notation "b"=>right.value V

private theorem equal_geometric_receipt
    (HL :left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR :right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (hequal :a=b)
    (p :Fin ((P).ambient c+1)→ℝ) (HS :p∈slice Q (d).frame V)
    (Hh :p h=a)
    (Hgrad :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0):
    ∃R :CanonicalPair hn ht ha hR0 old hv hd left right,∀side,
      ∃u :ℕ→ℝ,(canonicalObservation hn ht ha hR0 old hv hd left right R side).Roots u ∧
        PhysicalReadback hn ht ha hR0 old hv hd left right R side u p p ∧
        ∀idx :Index (Fin 0) cs,u (enumerate cs idx).val=z idx:=
  exists_physical_equal_level_at_state (n:=(P).ambient c) (S:=(P).cap c+1) (B:=(P).width c) («Q»:=Q)
    (initial P PLAN c) hQ cs ho x (by unfold IntegralMixedRoadmapRetainedAppend.parentState;rfl)
    d hk g hg (IntegralMixedRoadmapProperParent.objective_value hn ht ha hR0 old hv hd)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha c) _
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) c)
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c) z
    (IntegralMixedRoadmapRetainedAppend.parent_roots hn ht ha hR0 old hv hd E he)
    phi (IntegralMixedRoadmapProperParent.hom_generators hn ht ha hR0 old hv hd)
    V (IntegralMixedRoadmapProperParent.hom_values hn ht ha hR0 old hv hd)
    (canonical_level_horizon hn ht ha hR0 old hv hd) choices left right HL HR hequal p HS Hh Hgrad

/-- The actual old node and a weak child-critical boundary point supply one
guarded pair and both natural programs at the same physical point. -/
theorem exists_equal_geometric_level
    (HL :left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR :right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (hequal :a=b)
    (p :Fin ((P).ambient c+1)→ℝ) (HS :p∈slice Q (d).frame V)
    (Hh :p h=a)
    (Hgrad :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0):
    ∃R :CanonicalPair hn ht ha hR0 old hv hd left right,∀side,
      ∃u :ℕ→ℝ,(canonicalObservation hn ht ha hR0 old hv hd left right R side).Roots u ∧
        PhysicalReadback hn ht ha hR0 old hv hd left right R side u p p ∧
        ∀idx,idx<arity cs→u idx=oldNatural hn ht ha hR0 old hv idx:=by
  obtain ⟨R,HE⟩:=equal_geometric_receipt hn ht ha hR0 old hv hd left right HL HR hequal p HS Hh Hgrad
  refine ⟨R,?_⟩
  intro side
  obtain ⟨u,hu,HN,hOld⟩:=HE side
  refine ⟨u,?_,?_,equal_old_raw_from_typed hn ht ha hR0 old hv hd u hOld⟩
  · exact hu
  · exact HN

/-- Every allowed equal-height boundary point with the child critical
equations has a fresh fully accepted history on each child side. -/
theorem exists_equal_accepted_level
    (HL :left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR :right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (hequal :a=b)
    (p :Fin ((P).ambient c+1)→ℝ) (HS :p∈slice Q (d).frame V)
    (Hh :p h=a)
    (Hgrad :∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0):
    ∃R :CanonicalPair hn ht ha hR0 old hv hd left right,∀side,
      ∃w,∃hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
        (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old R.leftSpec R.rightSpec side w),
        HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0
          (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old R.leftSpec R.rightSpec side w) hV) p ∧
        IntegralMixedRoadmapProper.Midpoint hn ht ha hR0
          (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old R.leftSpec R.rightSpec side w):=by
  obtain ⟨R,HE⟩:=exists_equal_geometric_level hn ht ha hR0 old hv hd left right HL HR hequal p HS Hh Hgrad
  refine ⟨R,?_⟩
  intro side
  obtain ⟨u,hu,HN,hOld⟩:=HE side
  exact exists_accepted_word hn ht ha hR0 old hv hd left right R side u hu p p HN hOld

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
