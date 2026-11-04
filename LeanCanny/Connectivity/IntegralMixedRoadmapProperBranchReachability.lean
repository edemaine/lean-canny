/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapProperEdgeConstruct
public import LeanCanny.Connectivity.IntegralMixedRoadmapPointReachability
public import LeanCanny.Connectivity.IntegralMixedRoadmapFrozenSliceTransport
/-! # Actual matched branches generate native reachability of entire points -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedFrozenFrame IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedFramedPhysicalIndex (arity enumerate)
open IntegralMixedRoadmapProperAppend
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.point
  IntegralMixedRoadmapAtomic.dimension pointAt canonicalPointAt

private theorem branch_cast_heq {a b :ℕ} (h :a=b) (p :Fin a→ℝ) :
    HEq p (fun i :Fin b=>p (Fin.cast h.symm i)):=by
  cases h
  rfl

/-- A constructed whole-point readback is interpreted in the common original
source, without reusing its word or ordinal in another sampler. -/
theorem pointAt_eq_canonical_of_point_heq (old q :List Bool)
    (hq :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=IntegralMixedRoadmapAtomic.candidate old)
    (p :Fin ((P).ambient (IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old
      (IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old))+1)→ℝ)
    (HP :HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hq) p) :
    pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) q hq hc=
      canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p:=by
  have HG :HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hq)
      (pointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) q hq hc):=by
    unfold pointAt
    exact branch_cast_heq (congrArg (·+1) (ambient_eq hn ht ha hR0 _ q hc)) _
  have HC :HEq p (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl p):=by
    unfold canonicalPointAt
    exact branch_cast_heq (congrArg (·+1) (canonical_ambient_eq hn ht ha hR0 _ old rfl)) _
  exact eq_of_heq (HG.symm.trans (HP.trans HC))

section Branch
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
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
noncomputable local instance properBranchReachabilityIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
attribute [local irreducible] IntegralMixedMarkedReservedParent.bank
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
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

variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
local notation "a"=>left.value V
local notation "b"=>right.value V

theorem proper_branch_point_reachable
    (HL :left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR :right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (hab :a<b)
    (havoid :∀v,v∈Set.Ioo a b→v∉IntegralMixedSelectedCriticalCuts.bad x hm
      (cutRule x (d).frame h g hg) phi choices)
    (hheight :Disjoint (Set.Ioo a b) (realCriticalValues Q (line (d).frame h) V h))
    (M :MatchedSlabInterior x hm phi (line (d).frame h) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (fiber :IntegralMixedSelectedPhysicalFiber.physical (cutSource x (d).frame h) hm
      (cutRule x (d).frame h g hg) phi ((a+b)/2)):
    let rho:=FrozenCoordinateOrdering.permutation (line (d).frame h).frozen
    PointReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old)
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl (M.curve fiber a∘rho.symm))
      (canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl (M.curve fiber b∘rho.symm)):=by
  dsimp only
  have HP:=exists_proper_pair hn ht ha hR0 old hv hd left right HL HR hab havoid hheight M fiber
  obtain ⟨R,wL,wR,hVL,hVR,hPL,hPR,hProper⟩:=HP
  let qL:=packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old R.leftSpec R.rightSpec false wL
  let qR:=packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old R.leftSpec R.rightSpec true wR
  have HCL :IntegralMixedRoadmapAtomic.candidate qL=IntegralMixedRoadmapAtomic.candidate old:=candidate_packet _ _ _ _ _ _
  have HCR :IntegralMixedRoadmapAtomic.candidate qR=IntegralMixedRoadmapAtomic.candidate old:=candidate_packet _ _ _ _ _ _
  have HE :IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0 qL qR:=Or.inr hProper
  have HRaw :RawReachable hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) qL qR:=
    ⟨hVL,hVR,HCL,HCR,Relation.ReflTransGen.single HE⟩
  have HLPoint:=pointAt_eq_canonical_of_point_heq hn ht ha hR0 old qL hVL HCL _ hPL
  have HRPoint:=pointAt_eq_canonical_of_point_heq hn ht ha hR0 old qR hVR HCR _ hPR
  have HReach:=point_reachable_of_raw hn ht ha hR0 hVL hVR HCL HCR HRaw
  exact (congrArg₂ (PointReachable hn ht ha hR0 _) HLPoint HRPoint).mp HReach

end Branch
end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
