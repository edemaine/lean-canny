/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendBase
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendCriticalFree
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendCoordinates
/-! # Genuine matched slab geometry gives complete actual native Local incidence -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedChronologicalSweepFrame IntegralMixedFramedHistoryScript
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
variable {old : List Bool} {hv : FormulaSignSlotRadialProviderAtomic.Valid old}
  {hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
local notation "E" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "x" => FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd E he
local notation "hm" => FormulaSignSlotRadialProviderRetainedAppend.parent_horizon old hv hd E he
local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd E he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd E he
local notation "V" => FormulaSignSlotRadialProviderRetainedAppend.parentValues old hv hd E he
local notation "phi" => FormulaSignSlotRadialProviderRetainedAppend.parentHom old hv hd E he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd E he
local notation "hg" => FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd E he
local notation "h" => next d hk
local notation "choices" => FormulaSignSlotRadialProviderRetainedAppend.levelChoices old hv hd E he
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source

local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old E
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd E he
noncomputable local instance providerProperAppendLocalIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.levelChoices
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.depth
local notation "a" => left.value V
local notation "b" => right.value V

theorem SampledLevel.local_of_matched_branch
    (hab : a<b)
    (havoid : ∀v,v∈Set.Ioo a b→v∉IntegralMixedSelectedCriticalCuts.bad x hm (cutRule x (d).frame h g hg) phi choices)
    (hheight : Disjoint (Set.Ioo a b) (realCriticalValues (FormulaSignSlotRadialProviderRecordPlan.spatial c)
      (line (d).frame h) V h))
    (M : MatchedSlabInterior x hm phi (line (d).frame h) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (fiber : IntegralMixedSelectedPhysicalFiber.physical (cutSource x (d).frame h) hm
      (cutRule x (d).frame h g hg) phi ((a+b)/2))
    (S : SampledLevel old hv hd left right R side
      (M.curve fiber ((a+b)/2)∘(FrozenCoordinateOrdering.permutation (line (d).frame h).frozen).symm)
      (M.curve fiber (if side then b else a)∘(FrozenCoordinateOrdering.permutation (line (d).frame h).frozen).symm)) :
    FormulaSignSlotRadialProviderLocalEdge.Local
      (packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec side S.receipt.word) := by
  have HA := S.all_coordinates_of_matched_branch hab M fiber
  refine ⟨S.atomic_valid,S.base hab havoid,S.no_critical hheight,?_⟩
  cases side
  · exact Or.inl HA
  · exact Or.inr HA

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
