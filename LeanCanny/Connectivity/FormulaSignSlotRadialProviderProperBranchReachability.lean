/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphCanonicalPoints
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphSymmetry
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderProperEdgeConstruct
/-! # A genuine canonical slab branch yields an actual native proper edge -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Encoding
open LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
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
noncomputable local instance providerProperBranchIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.levelChoices

variable (left right : ParentEndpoint old hv hd)
local notation "a" => left.value V
local notation "b" => right.value V

theorem proper_branch_point_reachable
    (HL : left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR : right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (hab : a<b)
    (havoid : ∀v,v∈Set.Ioo a b→v∉IntegralMixedSelectedCriticalCuts.bad x hm (cutRule x (d).frame h g hg) phi choices)
    (hheight : Disjoint (Set.Ioo a b) (realCriticalValues (Q r) (line (d).frame h) V h))
    (M : MatchedSlabInterior x hm phi (line (d).frame h) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (fiber : IntegralMixedSelectedPhysicalFiber.physical (cutSource x (d).frame h) hm (cutRule x (d).frame h g hg) phi ((a+b)/2)) :
    let rho := FrozenCoordinateOrdering.permutation (line (d).frame h).frozen
    PointReachable (FormulaSignSlotRadialProviderAtomic.provider old)
      (providerPoint old (M.curve fiber a∘rho.symm)) (providerPoint old (M.curve fiber b∘rho.symm)) := by
  dsimp only
  obtain ⟨R,wL,wR,hVL,hVR,hPL,hPR,hProper⟩ :=
    FormulaSignSlotRadialProviderProperEdgeConstruct.exists_proper_pair old hv hd left right HL HR hab havoid hheight M fiber
  let qL := packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec false wL
  let qR := packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec true wR
  have HCL : FormulaSignSlotRadialProviderAtomic.provider qL=FormulaSignSlotRadialProviderAtomic.provider old := provider_packet _ _ _ _ _ _
  have HCR : FormulaSignSlotRadialProviderAtomic.provider qR=FormulaSignSlotRadialProviderAtomic.provider old := provider_packet _ _ _ _ _ _
  exact ⟨qL,qR,hVL,hVR,HCL,HCR,
    (providerPoint_eq_pointAt_of_native_heq old qL hVL HCL _ hPL).symm,
    (providerPoint_eq_pointAt_of_native_heq old qR hVR HCR _ hPR).symm,
    hVL,hVR,HCL,HCR,Relation.ReflTransGen.single (Or.inr hProper)⟩

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
