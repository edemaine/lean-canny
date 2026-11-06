/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendGeometry
public import LeanCanny.Geometry.IntegralMixedChronologicalGuardedProperLevelState
/-! # Allowed equal-height endpoints construct coherent actual provider tuples -/
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
noncomputable local instance providerEqualAppendGeometryIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentValues
  FormulaSignSlotRadialProviderRetainedAppend.parentHom FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.levelChoices
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth

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

private theorem equal_geometric_receipt
    (HL : left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR : right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (hequal : a=b) (p : Fin ((P).ambient c+1)→ℝ) (HS : p∈slice Q (d).frame V)
    (Hh : p h=a)
    (Hgrad : ∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    ∃R : CanonicalPair old hv hd left right,∀side,
      ∃u : ℕ→ℝ,(canonicalObservation old hv hd left right R side).Roots u ∧
        PhysicalReadback old hv hd left right R side u p p ∧
        ∀idx : Index (Fin 0) cs,u (enumerate cs idx).val=z idx :=
  exists_physical_equal_level_at_state (n:=(P).ambient c) (S:=(P).cap c+1) (B:=(P).width c) («Q»:=Q)
    (initial P PLAN c) hQ cs ho x (by unfold FormulaSignSlotRadialProviderRetainedAppend.parentState;rfl)
    d hk g hg rfl (FormulaSignSlotRadialProviderRecordPlan.positive c) _
    (FormulaSignSlotRadialProviderRetainedAppend.degree_power old E)
    (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap c) z
    (FormulaSignSlotRadialProviderRetainedAppend.parent_roots old hv hd E he)
    phi (FormulaSignSlotRadialProviderRetainedAppend.parentHom_generators old hv hd E he)
    V (FormulaSignSlotRadialProviderRetainedAppend.parentHom_quotients old hv hd E he)
    (FormulaSignSlotRadialProviderRetainedAppend.equal_horizon old hv hd E he) choices left right HL HR hequal p HS Hh Hgrad

theorem exists_equal_geometric_level
    (HL : left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR : right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (hequal : a=b) (p : Fin ((P).ambient c+1)→ℝ) (HS : p∈slice Q (d).frame V)
    (Hh : p h=a)
    (Hgrad : ∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    ∃R : CanonicalPair old hv hd left right,∀side,
      ∃u : ℕ→ℝ,(canonicalObservation old hv hd left right R side).Roots u ∧
        PhysicalReadback old hv hd left right R side u p p ∧
        ∀idx,idx<arity cs→u idx=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv idx := by
  obtain ⟨R,HE⟩ := equal_geometric_receipt old hv hd left right HL HR hequal p HS Hh Hgrad
  refine ⟨R,?_⟩
  intro side
  obtain ⟨u,hu,HN,hOld⟩ := HE side
  exact ⟨u,hu,HN,old_raw_from_typed old hv hd u hOld⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
