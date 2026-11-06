/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphCanonicalGeometry
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendCodes
public import LeanCanny.Geometry.IntegralMixedOptionalEndpointCriticalPaths
/-! # Actual allowed endpoint fibers contain joined weak child-critical samples -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity
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
noncomputable local instance providerEndpointCriticalIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.levelChoices

theorem exists_joined_allowed_endpoint_critical (endpoint : ParentEndpoint old hv hd)
    (HAllowed : endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (p : Fin ((P).ambient r+1)→ℝ) (HP : p∈slice (Q r) (d).frame V) (Hph : p h=endpoint.value V) :
    ∃q : Fin ((P).ambient r+1)→ℝ,
      JoinedIn (slice (Q r) (d).frame V∩{y |y h=endpoint.value V}) p q ∧
      q∈slice (Q r) (d).frame V ∧ q h=endpoint.value V ∧
      ∀i,i∉insert h (d).frame.frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
          (Int.castRingHom ℝ) q=0 := by
  obtain ⟨R,_⟩ := FormulaSignSlotRadialProviderProperParent.exists_guarded_pair old hv hd endpoint endpoint HAllowed HAllowed
  have HR : (cs).length+R.result.commands.length+((P).ambient r-(d).frame.frozen.card)≤(P).cap r+1+1 := by
    have H := FormulaSignSlotRadialProviderRetainedAppend.equal_horizon old hv hd E he
    have HC := R.result.count
    rw [(d).frozen_card]
    omega
  exact R.result.exists_joined_endpoint_critical h
    (IntegralMixedChronologicalSweepFrame.next_free d hk) (d).frozen_card.symm g hg
    (FormulaSignSlotRadialProviderRetainedAppend.charge old)
    (FormulaSignSlotRadialProviderRetainedAppend.degree_power old E)
    (FormulaSignSlotRadialProviderGraph.parent_source_proper old hv) HR false p HP Hph

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
