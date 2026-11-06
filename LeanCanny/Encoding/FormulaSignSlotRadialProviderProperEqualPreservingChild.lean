/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperEqualAppendGeometry
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendConstruct
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendWordReceipt
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPaddingPoint
/-! # Allowed endpoint fibers construct accepted children preserving every earlier field -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Connectivity IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalEndpoint
open IntegralMixedChronologicalFrame IntegralMixedFrozenFrame IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep
open IntegralMixedFramedPhysicalIndex (arity)
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
noncomputable local instance providerEqualChildIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor FormulaSignSlotRadialProviderRetainedAppend.parentValues
  FormulaSignSlotRadialProviderRetainedAppend.parentHom FormulaSignSlotRadialProviderRetainedAppend.levelChoices
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth

theorem exists_equal_preserving_child (endpoint : ParentEndpoint old hv hd)
    (HAllowed : endpoint.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (p : Fin ((P).ambient c+1)→ℝ) (HS : p∈slice (FormulaSignSlotRadialProviderRecordPlan.spatial c) (d).frame V)
    (Hh : p h=endpoint.value V)
    (HG : ∀i,i∉insert h (d).frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial
        (FormulaSignSlotRadialProviderRecordPlan.spatial c).low
        (FormulaSignSlotRadialProviderRecordPlan.spatial c).leading
        (FormulaSignSlotRadialProviderRecordPlan.spatial c).degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    ∃child,∃hChild : FormulaSignSlotRadialProviderAtomic.Valid child,
      FormulaSignSlotRadialProviderAtomic.provider child=FormulaSignSlotRadialProviderAtomic.provider old ∧
      FormulaSignSlotRadialProviderAtomic.depth child=FormulaSignSlotRadialProviderAtomic.depth old+1 ∧
      HEq (FormulaSignSlotRadialProviderAtomic.point child hChild) p ∧
      ∀b,b<FormulaSignSlotRadialProviderAtomic.initial old+start old→
        FormulaSignSlotRadialProviderAtomic.field child hChild b=FormulaSignSlotRadialProviderAtomic.field old hv b := by
  obtain ⟨R,HE⟩ := exists_equal_geometric_level old hv hd endpoint endpoint HAllowed HAllowed rfl p HS Hh HG
  obtain ⟨u,hu,HN,hOld⟩ := HE false
  obtain ⟨p0,hp0,hg0⟩ := exists_padding_critical old hv R.leftSpec R.rightSpec false
  obtain ⟨W⟩ := exists_word_receipt old hv hd endpoint endpoint R false u hu p0 hp0 hg0
  let S : SampledLevel old hv hd endpoint endpoint R false p p := ⟨u,HN,hOld,p0,W⟩
  exact ⟨packet (FormulaSignSlotRadialProviderAtomic.dimension old) old R.leftSpec R.rightSpec false W.word,
    S.atomic_valid,provider_packet _ _ _ _ _ _,depth_packet _ _ _ _ _ _,
    S.point_heq S.atomic_valid,S.accepted_old_fields⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
