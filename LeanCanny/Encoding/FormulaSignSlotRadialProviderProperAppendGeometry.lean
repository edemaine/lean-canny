/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendObservation
public import LeanCanny.Geometry.IntegralMixedChronologicalGuardedProperLevelState
/-! # Genuine provider slab geometry constructs one coherent proper-level tuple family -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Connectivity LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedFrozenFrame IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedFramedPhysicalIndex (arity enumerate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "PLAN" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "E" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old E
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd E he
local notation "ho" => FormulaSignSlotRadialProviderRetainedAppend.parent_room old hv hd E he
local notation "x" => FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd E he
local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd E he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd E he
local notation "z" => FormulaSignSlotRadialProviderRetainedAppend.parentTuple old hv hd E he
local notation "V" => FormulaSignSlotRadialProviderRetainedAppend.parentValues old hv hd E he
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial c
local notation "hQ" => IntegralMixedStaticRecordPrefix.cap Q (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap c)
local notation "phi" => FormulaSignSlotRadialProviderRetainedAppend.parentHom old hv hd E he
local notation "hm" => FormulaSignSlotRadialProviderRetainedAppend.parent_horizon old hv hd E he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd E he
local notation "hg" => FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd E he
local notation "h" => IntegralMixedChronologicalSweepFrame.next d hk
local notation "choices" => FormulaSignSlotRadialProviderRetainedAppend.levelChoices old hv hd E he
noncomputable local instance providerProperGeometryIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentValues
  FormulaSignSlotRadialProviderRetainedAppend.parentHom FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.levelChoices
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth

section Readback
variable (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
include side in
theorem physical_horizon : (cs).length+R.result.commands.length+2+2*(R.orderedFree hk).length≤(P).cap c+1+1 := by
  have H := canonical_program_room old hv hd left right R side
  rw [R.levelCommands_length] at H
  omega
noncomputable def PhysicalReadback (u : ℕ→ℝ) (pMID pChild : Fin ((P).ambient c+1)→ℝ) : Prop :=
  NativePair.PhysicalReadback hQ cs R hk g hg side
    (physical_horizon old hv hd left right R side)
    (canonicalObservation old hv hd left right R side).arity u pMID pChild
    (fun idx=>(canonicalObservation old hv hd left right R side).point u idx)
end Readback

private theorem old_raw_from_typed (u :ℕ→ℝ)
    (H :∀idx :Index (Fin 0) cs,u (enumerate cs idx).val=z idx):
    ∀idx,idx<arity cs→u idx=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv idx:=by
  intro idx hi
  let typed:Index (Fin 0) cs:=(enumerate cs).symm ⟨idx,hi⟩
  have HE :(enumerate cs typed).val=idx:=by
    exact congrArg Fin.val ((enumerate cs).apply_symm_apply ⟨idx,hi⟩)
  have HZ :z typed=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv idx:=by
    unfold FormulaSignSlotRadialProviderRetainedAppend.parentTuple
    rw [HE]
  exact (congrArg u HE).symm.trans ((H typed).trans HZ)

variable (left right :ParentEndpoint old hv hd)
local notation "a"=>left.value V
local notation "b"=>right.value V

private theorem geometric_receipt
    (HL :left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR :right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (hab :a<b)
    (M :MatchedSlabInterior x hm phi (line (d).frame h) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (fiber :IntegralMixedSelectedPhysicalFiber.physical (cutSource x (d).frame h) hm
      (cutRule x (d).frame h g hg) phi ((a+b)/2)):
    let rho:=FrozenCoordinateOrdering.permutation (line (d).frame h).frozen
    let pMID:=M.curve fiber ((a+b)/2)∘rho.symm
    ∃R :CanonicalPair old hv hd left right,∀side,
      let pChild:=M.curve fiber (if side then b else a)∘rho.symm
      ∃u :ℕ→ℝ,(canonicalObservation old hv hd left right R side).Roots u ∧
        PhysicalReadback old hv hd left right R side u pMID pChild ∧
        ∀idx :Index (Fin 0) cs,u (enumerate cs idx).val=z idx:=
  exists_physical_proper_level_at_state (n:=(P).ambient c) (S:=(P).cap c+1) (B:=(P).width c) («Q»:=Q)
    (initial P PLAN c) hQ cs ho x (by unfold FormulaSignSlotRadialProviderRetainedAppend.parentState;rfl)
    d hk g hg (rfl)
    (FormulaSignSlotRadialProviderRecordPlan.positive c) _
    (FormulaSignSlotRadialProviderRetainedAppend.degree_power old E)
    (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap c) z
    (FormulaSignSlotRadialProviderRetainedAppend.parent_roots old hv hd E he)
    phi (FormulaSignSlotRadialProviderRetainedAppend.parentHom_generators old hv hd E he)
    V (FormulaSignSlotRadialProviderRetainedAppend.parentHom_quotients old hv hd E he)
    (FormulaSignSlotRadialProviderRetainedAppend.equal_horizon old hv hd E he) choices left right HL HR hab M fiber

/-- The actual old node and the genuine geometric slab supply ONE guarded
pair and ONE shared MID anchor, with both child natural witnesses. -/
theorem exists_geometric_level
    (HL :left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR :right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (hab :a<b)
    (M :MatchedSlabInterior x hm phi (line (d).frame h) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (fiber :IntegralMixedSelectedPhysicalFiber.physical (cutSource x (d).frame h) hm
      (cutRule x (d).frame h g hg) phi ((a+b)/2)):
    let rho:=FrozenCoordinateOrdering.permutation (line (d).frame h).frozen
    let pMID:=M.curve fiber ((a+b)/2)∘rho.symm
    ∃R :CanonicalPair old hv hd left right,∀side,
      let pChild:=M.curve fiber (if side then b else a)∘rho.symm
      ∃u :ℕ→ℝ,(canonicalObservation old hv hd left right R side).Roots u ∧
        PhysicalReadback old hv hd left right R side u pMID pChild ∧
        ∀idx,idx<arity cs→u idx=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv idx:=by
  dsimp only
  obtain ⟨R,HE⟩:=geometric_receipt old hv hd left right HL HR hab M fiber
  refine ⟨R,?_⟩
  intro side
  obtain ⟨u,hu,HN,hOld⟩:=HE side
  refine ⟨u,?_,?_,old_raw_from_typed old hv hd u hOld⟩
  · exact hu
  · exact HN

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
