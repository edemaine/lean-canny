/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPrefix
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendOwnPoint
/-! # The general provider append has the exact old canonical parent state -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial)
open FormulaSignSlotRadialProviderAtomic (dimension initial depth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "PLAN" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid

noncomputable def parentCommands (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :=
  FormulaSignSlotRadialProviderRecordContinuation.beforeCommands (preparedRoot old l r side) (start old)
    (prefix_fit old hv hd l r side hE)

theorem parent_length (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :
    (parentCommands old hv hd l r side hE).length=beginBirth old := by
  rw [parentCommands,FormulaSignSlotRadialProviderRecordContinuation.beforeCommands_length,prepared_initial,begin_eq_start]

theorem parent_room (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :
    (parentCommands old hv hd l r side hE).length≤(P).cap (preparedRoot old l r side)+1+1 := by
  rw [parentCommands,FormulaSignSlotRadialProviderRecordContinuation.beforeCommands_length]
  exact (FormulaSignSlotRadialProviderRecordPrefix.bound _ _ (prefix_fit old hv hd l r side hE)).trans (Nat.le_succ _)

noncomputable def parentState (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :=
  reframe (run (IntegralMixedFramedHistoryFamilyBits.initial P PLAN (preparedRoot old l r side))
    (parentCommands old hv hd l r side hE) (parent_room old hv hd l r side hE))
    (Q (preparedRoot old l r side))
    (IntegralMixedStaticRecordPrefix.cap (Q (preparedRoot old l r side))
      (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap (preparedRoot old l r side)))

private theorem snapshot_commands {n S B : ℕ} {V : SpatialSource n}
    (x : State V S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    IntegralMixedPrefixSnapshot.ofCommands x cs hc=IntegralMixedPrefixSnapshot.ofCommands x ds hd := by
  subst ds
  rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPrefix.snapshot parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentCommands

theorem snapshot_parent (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :
    FormulaSignSlotRadialProviderRecordPrefix.snapshot (preparedRoot old l r side) (start old)
      (prefix_fit old hv hd l r side hE)=
      IntegralMixedPrefixSnapshot.ofState (parentState old hv hd l r side hE) := by
  unfold FormulaSignSlotRadialProviderRecordPrefix.snapshot parentState
  apply snapshot_commands
  unfold parentCommands
  exact FormulaSignSlotRadialProviderRecordContinuation.before_commands _ _ (prefix_fit old hv hd l r side hE)

private theorem retained_snapshot_parent (old : List Bool) (hv : A old) (hd : depth old<dimension old) :
    FormulaSignSlotRadialProviderRecordPrefix.snapshot
      (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old (FormulaSignSlotRadialProviderAtomic.ownBirth old))
      (FormulaSignSlotRadialProviderRetainedAppend.start old)
      (FormulaSignSlotRadialProviderRetainedAppend.prefix_fit old hv hd _
        (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old))=
    IntegralMixedPrefixSnapshot.ofState
      (FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd _
        (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old)) := by
  unfold FormulaSignSlotRadialProviderRecordPrefix.snapshot FormulaSignSlotRadialProviderRetainedAppend.parentState
  apply snapshot_commands
  unfold FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  exact FormulaSignSlotRadialProviderRecordContinuation.before_commands _ _ _

private theorem state_heq (a b : IntegralMixedPrefixSnapshot.Data) (h : a=b) : HEq a.state b.state := by
  subst b
  rfl

theorem parent_snapshot_eq (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :
    IntegralMixedPrefixSnapshot.ofState (parentState old hv hd l r side hE)=
      IntegralMixedPrefixSnapshot.ofState
        (FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd _
          (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old)) := by
  have HN := prefix_snapshot old hv hd l r side hE (start old) le_rfl
  have HC := FormulaSignSlotRadialProviderRetainedAppend.prefix_snapshot old hv hd
    (FormulaSignSlotRadialProviderAtomic.ownBirth old)
    (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old) (start old) le_rfl
  exact (snapshot_parent old hv hd l r side hE).symm.trans
    (HN.trans (HC.symm.trans (retained_snapshot_parent old hv hd)))

theorem parent_state_heq (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :
    HEq (parentState old hv hd l r side hE)
      (FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd _
        (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old)) :=
  state_heq _ _ (parent_snapshot_eq old hv hd l r side hE)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
