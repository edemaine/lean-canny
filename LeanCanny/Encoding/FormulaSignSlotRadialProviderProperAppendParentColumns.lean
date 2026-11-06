/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendParent
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixMetadata
/-! # General appends preserve the canonical old physical column enumeration -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "PLAN" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
private theorem command_layout_heq {a b B C : ℕ} (ha : a=b) (hB : B=C)
    (cs : List (Instruction a B)) (ds : List (Instruction b C)) (he : HEq cs ds) :
    Index (Fin 0) cs=Index (Fin 0) ds ∧ arity cs=arity ds ∧ HEq (enumerate cs) (enumerate ds) := by
  subst b
  subst C
  cases eq_of_heq he
  exact ⟨rfl,rfl,HEq.rfl⟩
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
  (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r)
local notation "a" => preparedRoot old l r side
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "newCs" => parentCommands old hv hd l r side hE
local notation "oldCs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentCommands

theorem parent_commands_heq : HEq newCs oldCs := by
  have HP := (prepared_provider old l r side).trans
    (FormulaSignSlotRadialProviderRetainedAppend.prepared_provider old e).symm
  have HC := (prepared_count old hv hd l r side hE).trans
    (FormulaSignSlotRadialProviderRetainedAppend.prepared_count old hv hd e he).symm
  have HH := FormulaSignSlotRadialProviderRecordPrefix.commands_heq a c HP HC (start old)
    (prefix_fit old hv hd l r side hE) (fun i hi =>
      (prepared_record old hv l r side i hi).trans
        (FormulaSignSlotRadialProviderRetainedAppend.prepared_record old hv e i hi).symm)
  rw [FormulaSignSlotRadialProviderRecordContinuation.before_commands a (start old)
    (prefix_fit old hv hd l r side hE),
    FormulaSignSlotRadialProviderRecordContinuation.before_commands c (start old)
      (FormulaSignSlotRadialProviderRetainedAppend.prefix_fit old hv hd e he)] at HH
  unfold parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  exact HH

theorem parent_layout : Index (Fin 0) newCs=Index (Fin 0) oldCs ∧
    arity newCs=arity oldCs ∧ HEq (enumerate newCs) (enumerate oldCs) := by
  have HP := (prepared_provider old l r side).trans
    (FormulaSignSlotRadialProviderRetainedAppend.prepared_provider old e).symm
  exact command_layout_heq (FormulaSignSlotRadialProviderRecordPrefix.ambient a c HP)
    (FormulaSignSlotRadialProviderRecordPrefix.width a c HP) newCs oldCs
    (parent_commands_heq old hv hd l r side hE)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
