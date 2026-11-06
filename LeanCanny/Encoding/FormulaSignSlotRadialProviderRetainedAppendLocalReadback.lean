/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendWordReceipt
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelScalarValues
/-! # Both local blocks of the fresh retained witness read the chosen point -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedChronologicalEndpoint
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "cap" => FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentState parentTuple parentValues parentHom parentCommands parentDescriptor levelProgram levelObservation
variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {e : ℕ} {he : e<endBirth (dimension old) (N old) old}
  {p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ}

theorem WordReceipt.local_values (W : WordReceipt old hv hd e he p)
    (i : Fin ((parentCommands old hv hd e he).length+W.pair.result.commands.length+1+
      (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length+1+
      (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length)) :
    (levelObservation old hv hd e he W.pair false).point W.localTuple i.val=
      IntegralMixedChronologicalLevelScalarValues.levelValues p p W.pair.result.nextValues
        (childCoordinate old hv hd e he) (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)) i := by
  have H := W.local_readback.2.1
  unfold NativePair.PhysicalReadback at H
  obtain ⟨AM,EC,ordinal,hordinal,hN⟩ := H
  exact hN.bank_values i

theorem WordReceipt.local_powered (W : WordReceipt old hv hd e he p)
    (b : ℕ) (hb0 : (parentCommands old hv hd e he).length≤b)
    (hb1 : b<(parentCommands old hv hd e he).length+2+
      2*(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length)
    (i : Fin ((P).ambient (preparedRoot old e)+1)) :
    W.localTuple (arity (parentCommands old hv hd e he)+
      (2*FormulaSignSlotRadialProviderRecordPlan.parameters.ambient (preparedRoot old e)+4)*
      (b-(parentCommands old hv hd e he).length)+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot old e)+1)
        (2^(P).width (preparedRoot old e)) b=p i := by
  have H := W.local_readback.2.1
  unfold NativePair.PhysicalReadback at H
  obtain ⟨AM,EC,ordinal,hordinal,hN⟩ := H
  have HE := pair_commands_nil old hv hd e he W.pair
  have HLen : W.pair.result.commands.length=0 := congrArg List.length HE
  have HB0 : (parentCommands old hv hd e he).length+W.pair.result.commands.length≤b := by omega
  have HB1 : b<(parentCommands old hv hd e he).length+W.pair.result.commands.length+2+
      2*(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length := by omega
  have HB := NativePair.NaturalReadback.powered_block
    (IntegralMixedStaticRecordPrefix.cap (Q (preparedRoot old e)) (cap (preparedRoot old e)))
    (parentCommands old hv hd e he) W.pair (parent_descriptor_fit old hv hd e he)
    (childCoordinate old hv hd e he) (child_coordinate_free old hv hd e he) _ _ _ false _
    p p AM EC hN hordinal b HB0 HB1 i
  simpa only [HE,List.map_nil,List.nil_append,List.length_nil,Nat.add_zero,ite_self] using HB

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
