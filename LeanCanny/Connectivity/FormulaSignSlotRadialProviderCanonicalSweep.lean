/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphCanonicalGeometry
public import LeanCanny.Connectivity.IntegralMixedRoadmapCanonicalRetainedSweep
/-! # The actual accepted provider constructs its canonical finite matched sweeps -/
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
noncomputable local instance canonicalProviderSweepIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.levelChoices

theorem exists_canonical_matched_finite_sweep :
    Nonempty (MatchedFiniteSweep x hm phi (d).frame h g hg V
      (prefixInputChoices x hm (d).frame h g hg
        (IntegralMixedChronologicalSweepFrame.prefix_frozen d hk) phi choices)) := by
  have HR : (cs).length+2+((P).ambient r-(d).frame.frozen.card)≤(P).cap r+2 := by
    have H := FormulaSignSlotRadialProviderRetainedAppend.equal_horizon old hv hd E he
    rw [(d).frozen_card]
    omega
  obtain ⟨_,HS⟩ := exists_matched_finite_sweep x hm
    (FormulaSignSlotRadialProviderRecordPlan.positive r)
    (FormulaSignSlotRadialProviderRetainedAppend.charge old)
    (FormulaSignSlotRadialProviderRetainedAppend.degree_power old E)
    (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap r)
    (d).frame (d).free_normal (d).atomic (d).prefix_frozen h
    (IntegralMixedChronologicalSweepFrame.next_free d hk) (d).frozen_card.symm g hg
    (FormulaSignSlotRadialProviderRetainedAppend.parentTuple old hv hd E he)
    (FormulaSignSlotRadialProviderRetainedAppend.parent_roots old hv hd E he)
    phi (FormulaSignSlotRadialProviderRetainedAppend.parentHom_generators old hv hd E he)
    V (FormulaSignSlotRadialProviderRetainedAppend.parentHom_quotients old hv hd E he) choices HR
    (FormulaSignSlotRadialProviderGraph.parent_source_proper old hv)
  exact HS

theorem exists_canonical_retained_sweep (target : Fin (cs).length) :
    Nonempty (RetainedMatchedFiniteSweep x hm phi (d).frame h g hg V choices target) := by
  have HR : (cs).length+2+((P).ambient r-(d).frame.frozen.card)≤(P).cap r+1+1 := by
    have H := FormulaSignSlotRadialProviderRetainedAppend.equal_horizon old hv hd E he
    rw [(d).frozen_card]
    omega
  exact exists_retained_matched_finite_sweep x hm
    (FormulaSignSlotRadialProviderRecordPlan.positive r)
    (FormulaSignSlotRadialProviderRetainedAppend.charge old)
    (FormulaSignSlotRadialProviderRetainedAppend.degree_power old E)
    (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap r)
    (d).frame (d).free_normal (d).atomic (d).prefix_frozen h
    (IntegralMixedChronologicalSweepFrame.next_free d hk) (d).frozen_card.symm g hg
    (FormulaSignSlotRadialProviderRetainedAppend.parentTuple old hv hd E he)
    (FormulaSignSlotRadialProviderRetainedAppend.parent_roots old hv hd E he)
    phi (FormulaSignSlotRadialProviderRetainedAppend.parentHom_generators old hv hd E he)
    V (FormulaSignSlotRadialProviderRetainedAppend.parentHom_quotients old hv hd E he) choices target HR
    (FormulaSignSlotRadialProviderGraph.parent_source_proper old hv)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
