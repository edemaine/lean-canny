/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendLevel
/-! # Every represented retained pair has the literal appended endpoint bytes -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedChronologicalFrame IntegralMixedChronologicalEndpoint
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid

private theorem retained_spec {n B cap m current : ℕ} {labels s : List Bool}
    (h : IntegralMixedRoadmapEndpointSyntax.Good n B cap m current labels s)
    (hf : IntegralMixedRoadmapEndpointSyntax.fresh s=0) :
    s=IntegralMixedRoadmapEndpointSyntax.spec 0 (IntegralMixedRoadmapEndpointSyntax.field s 1) 0 0 0 0 := by
  have HK : IntegralMixedRoadmapEndpointSyntax.field s 0=0 := by
    by_contra H
    have HC := IntegralMixedRoadmapEndpointSyntax.fresh_eq_one H
    omega
  rcases h.2 with H|H|H
  · simpa only [IntegralMixedRoadmapEndpointSyntax.canonical,H.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2.1,H.2.2.2.2.2] using h.1
  · have HC := H.1
    omega
  · have HC := H.1
    omega

private theorem left_producer_retained {n S B m : ℕ} {V : SpatialSource n} {ι : Type} [Fintype ι]
    {x : State V S B m ι} {d : Descriptor n m} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {u v : Fin m}
    {hn : 0<n} {hc : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) V.degree≤2^B}
    (R : NativePair x d z φ values (.retained u) (.retained v) hn hc) :
    IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1=m-1-u.val := R.left_producer

private theorem right_producer_retained {n S B m : ℕ} {V : SpatialSource n} {ι : Type} [Fintype ι]
    {x : State V S B m ι} {d : Descriptor n m} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {u v : Fin m}
    {hn : 0<n} {hc : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) V.degree≤2^B}
    (R : NativePair x d z φ values (.retained u) (.retained v) hn hc) :
    IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1=m-1-v.val := R.right_producer

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderIntegerSource.source parentState parentTuple parentValues parentHom parentDescriptor

section Pair
variable (old : List Bool) (hv : A old) (hd : depth old<dimension old)
  (e : ℕ) (he : e<endBirth (dimension old) (N old) old)
variable (R : NativePair (parentState old hv hd e he) (parentDescriptor old hv hd e he) (parentTuple old hv hd e he)
  (parentHom old hv hd e he) (parentValues old hv hd e he)
  (.retained (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)))
  (.retained (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)))
  (FormulaSignSlotRadialProviderRecordPlan.positive (preparedRoot old e))
  (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap (preparedRoot old e)))

private theorem producer_reference : (parentCommands old hv hd e he).length-1-
    (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)).val=e := by
  change (parentCommands old hv hd e he).length-1-((parentCommands old hv hd e he).length-1-e)=e
  have H : e<(parentCommands old hv hd e he).length := by rw [parent_length];exact he
  omega

theorem left_spec : R.leftSpec=endpoint e := by
  have H := retained_spec R.left_good (by simpa only [IntegralMixedOptionalEndpoints.Endpoint.freshCount] using R.left_fresh)
  have HP := (left_producer_retained R).trans (producer_reference old hv hd e he)
  rw [H,HP]
  rfl

theorem right_spec : R.rightSpec=endpoint e := by
  have H := retained_spec R.right_good (by simpa only [IntegralMixedOptionalEndpoints.Endpoint.freshCount] using R.right_fresh)
  have HP := (right_producer_retained R).trans (producer_reference old hv hd e he)
  rw [H,HP]
  rfl

theorem pair_commands_nil : R.result.commands=[] := by
  apply List.eq_nil_of_length_eq_zero
  simpa only [IntegralMixedOptionalEndpoints.Endpoint.freshCount,Nat.add_zero] using R.count

theorem level_packet : R.levelPacket false=IntegralMixedRoadmapLevel.packet
    (FormulaSignSlotRadialProviderAtomic.frozen old) (endpoint e) (endpoint e) false [] := by
  unfold NativePair.levelPacket
  rw [parent_labels,left_spec old hv hd e he R,right_spec old hv hd e he R]

theorem level_codes : WordList.encode (R.levelCodes (parent_descriptor_fit old hv hd e he)
    (childCoordinate old hv hd e he) (child_coordinate_free old hv hd e he) false).reverse=
    IntegralMixedRoadmapLevel.compiled (dimension old)
      (IntegralMixedRoadmapLevel.packet (FormulaSignSlotRadialProviderAtomic.frozen old)
        (endpoint e) (endpoint e) false []) := by
  have H := R.levelWord_compiled (parent_descriptor_fit old hv hd e he)
    (childCoordinate old hv hd e he) (child_coordinate_free old hv hd e he) rfl false
  rw [level_packet old hv hd e he R] at H
  exact H.trans (congrArg (fun n=>IntegralMixedRoadmapLevel.compiled n
    (IntegralMixedRoadmapLevel.packet (FormulaSignSlotRadialProviderAtomic.frozen old)
      (endpoint e) (endpoint e) false [])) (prepared_dimension old e))

end Pair
end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
