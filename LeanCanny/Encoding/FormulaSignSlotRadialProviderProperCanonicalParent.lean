/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendCaptures
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendOwnPoint
public import LeanCanny.Geometry.IntegralMixedChronologicalGuardedPair
/-! # The actual old provider word constructs its canonical guarded endpoint pair -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperParent
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalEndpoint
open IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
open FormulaSignSlotRadialProviderAtomic (dimension depth)
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old) (hd : depth old<dimension old)
local notation "ep" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "hep" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "root" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old ep
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd ep hep
local notation "x" => FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd ep hep
local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd ep hep
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd ep hep
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd ep hep
local notation "hg" => FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd ep hep
local notation "z" => FormulaSignSlotRadialProviderRetainedAppend.parentTuple old hv hd ep hep
local notation "phi" => FormulaSignSlotRadialProviderRetainedAppend.parentHom old hv hd ep hep
local notation "values" => FormulaSignSlotRadialProviderRetainedAppend.parentValues old hv hd ep hep
local notation "hm" => FormulaSignSlotRadialProviderRetainedAppend.parent_horizon old hv hd ep hep
local notation "choices" => FormulaSignSlotRadialProviderRetainedAppend.levelChoices old hv hd ep hep
local notation "hcap" => FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap root
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentHom FormulaSignSlotRadialProviderRetainedAppend.parentValues

noncomputable local instance providerProperParentIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs

noncomputable abbrev Pair (left right : Endpoint (cs).length) :=
  NativePair x d z phi values left right (FormulaSignSlotRadialProviderRecordPlan.positive root) hcap

noncomputable def endpointSet : Set ℝ :=
  jointEndpointSet x hm phi (d).frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg values choices

theorem parent_room : (cs).length+1≤(P).cap root+1 := by
  have H := FormulaSignSlotRadialProviderRetainedAppend.equal_horizon old hv hd ep hep
  omega

theorem exists_guarded_pair (left right : Endpoint (cs).length)
    (hleft : left.Allowed (endpointSet old hv hd)) (hright : right.Allowed (endpointSet old hv hd)) :
    ∃R : Pair old hv hd left right,
      GuardedProgram x (FormulaSignSlotRadialProviderRecordPlan.positive root) hcap z phi values
        R.result.commands R.result.room R.result.codes R.result.tuple R.result.hom R.result.nextValues := by
  exact optional_pair_guarded x hm (parent_room old hv hd)
    (FormulaSignSlotRadialProviderRecordPlan.positive root)
    (FormulaSignSlotRadialProviderRetainedAppend.charge old)
    (FormulaSignSlotRadialProviderRetainedAppend.degree_power old ep) hcap d hk g hg rfl z
    (FormulaSignSlotRadialProviderRetainedAppend.parent_roots old hv hd ep hep) phi
    (FormulaSignSlotRadialProviderRetainedAppend.parentHom_generators old hv hd ep hep) values
    (FormulaSignSlotRadialProviderRetainedAppend.parentHom_quotients old hv hd ep hep)
    choices left right hleft hright

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperParent
