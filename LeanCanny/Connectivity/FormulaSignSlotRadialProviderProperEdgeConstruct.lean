/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendLocal
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendMidSignature
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderEdge
/-! # A genuine matched slab constructs two own accepted native proper endpoints -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderProperEdgeConstruct
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Encoding
open FormulaSignSlotRadialProviderProperAppend IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalEndpoint
open IntegralMixedChronologicalFrame IntegralMixedFrozenFrame IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "E" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old E
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
noncomputable local instance providerProperEdgeConstructIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor FormulaSignSlotRadialProviderRetainedAppend.parentValues
  FormulaSignSlotRadialProviderRetainedAppend.parentHom FormulaSignSlotRadialProviderRetainedAppend.levelChoices
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth

variable (left right : ParentEndpoint old hv hd)
local notation "a" => left.value V
local notation "b" => right.value V
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial c
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
    ∃R :CanonicalPair old hv hd left right,∃wL wR,
      ∃hVL :FormulaSignSlotRadialProviderAtomic.Valid
        (packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec false wL),
      ∃hVR :FormulaSignSlotRadialProviderAtomic.Valid
        (packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec true wR),
        HEq (FormulaSignSlotRadialProviderAtomic.point
          (packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec false wL) hVL)
          (M.curve fiber a∘rho.symm) ∧
        HEq (FormulaSignSlotRadialProviderAtomic.point
          (packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec true wR) hVR)
          (M.curve fiber b∘rho.symm) ∧
        FormulaSignSlotRadialProviderEdge.Proper
          (pair (packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec false wL)
            (packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec true wR)) := by
  dsimp only
  obtain ⟨R,HS⟩ := exists_sampled_level old hv hd left right HL HR hab M fiber
  obtain ⟨SL⟩ := HS false
  obtain ⟨SR⟩ := HS true
  have HPL : HEq (FormulaSignSlotRadialProviderAtomic.point
      (packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec false SL.receipt.word)
      SL.atomic_valid) (M.curve fiber a∘(FrozenCoordinateOrdering.permutation (line (d).frame h).frozen).symm) := by
    simpa only [Bool.false_eq_true,ite_false] using SL.point_heq SL.atomic_valid
  have HPR : HEq (FormulaSignSlotRadialProviderAtomic.point
      (packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec true SR.receipt.word)
      SR.atomic_valid) (M.curve fiber b∘(FrozenCoordinateOrdering.permutation (line (d).frame h).frozen).symm) := by
    simpa only [ite_true] using SR.point_heq SR.atomic_valid
  refine ⟨R,SL.receipt.word,SR.receipt.word,SL.atomic_valid,SR.atomic_valid,HPL,HPR,?_⟩
  refine ⟨?_,?_,?_,?_⟩
  · simp only [FormulaSignSlotRadialProviderIdentity.SameProvider,FormulaSignSlotRadialProviderIdentity.left,
      FormulaSignSlotRadialProviderIdentity.right,pairFst_pair,pairSnd_pair,provider_packet]
  · simpa only [pairFst_pair] using
      SampledLevel.local_of_matched_branch hab havoid hheight M fiber SL
  · simpa only [pairSnd_pair] using
      SampledLevel.local_of_matched_branch hab havoid hheight M fiber SR
  · exact SL.midpoint_signature SR

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderProperEdgeConstruct
