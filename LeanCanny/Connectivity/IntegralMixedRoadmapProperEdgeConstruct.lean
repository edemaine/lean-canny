/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLocal
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendGeometry
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendSampledExtension
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendMidSignature
/-! # Genuine matched branches construct actual native proper edges -/
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
noncomputable local instance properEdgeConstructIndexFintype :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs
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

variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
local notation "a"=>left.value V
local notation "b"=>right.value V

theorem exists_proper_pair
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
    ∃R :CanonicalPair hn ht ha hR0 old hv hd left right,∃wL wR,
      ∃hVL :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
        (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old R.leftSpec R.rightSpec false wL),
      ∃hVR :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
        (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old R.leftSpec R.rightSpec true wR),
        HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0
          (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old R.leftSpec R.rightSpec false wL) hVL)
          (M.curve fiber a∘rho.symm) ∧
        HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0
          (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old R.leftSpec R.rightSpec true wR) hVR)
          (M.curve fiber b∘rho.symm) ∧
        IntegralMixedRoadmapEdge.Proper hn ht ha hR0
          (pair (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old R.leftSpec R.rightSpec false wL)
            (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old R.leftSpec R.rightSpec true wR)):=by
  dsimp only
  obtain ⟨R,HF⟩:=exists_geometric_level hn ht ha hR0 old hv hd left right HL HR hab M fiber
  obtain ⟨uL,huL,NL,hOldL⟩:=HF false
  obtain ⟨uR,huR,NR,hOldR⟩:=HF true
  obtain ⟨p0L,WL,hVL,hPL,hML⟩:=exists_accepted_receipt hn ht ha hR0 old hv hd left right R false uL huL _ _ NL hOldL
  obtain ⟨p0R,WR,hVR,hPR,hMR⟩:=exists_accepted_receipt hn ht ha hR0 old hv hd left right R true uR huR _ _ NR hOldR
  refine ⟨R,WL.word,WR.word,hVL,hVR,hPL,hPR,?_⟩
  refine ⟨?_,?_,?_,?_⟩
  · simp only [IntegralMixedRoadmapIdentity.SameCandidate,IntegralMixedRoadmapIdentity.left,
      IntegralMixedRoadmapIdentity.right,pairFst_pair,pairSnd_pair,candidate_packet]
  · simpa only [pairFst_pair] using
      WL.local_of_matched_branch hn ht ha hR0 old hv hd left right R false hab M fiber NL hOldL havoid hheight
  · simpa only [pairSnd_pair] using
      WR.local_of_matched_branch hn ht ha hR0 old hv hd left right R true hab M fiber NR hOldR havoid hheight
  · exact WL.midpoint_signature hn ht ha hR0 old hv hd left right R WR _ _ _ NL NR hVL hVR

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
