/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPrefix
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCanonicalEndpoints
/-! # The general appended parent is the actual canonical old typed state -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (left right :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old left right)
local notation "r"=>preparedRoot hn ht ha hR0 old left right side
local notation "j"=>start hn ht ha hR0 old
local notation "hj"=>prepared_start_fit hn ht ha hR0 old hv hd left right side hE
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "cj"=>IntegralMixedRoadmapRetainedAppend.prefix_fit hn ht ha hR0 old hv hd e he
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank preparedRoot
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentState IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedFramedRawHeight.rootCeiling
  IntegralMixedFramedNormalizationBits.requiredModulus IntegralMixedExceptionalBounds.auxiliaryCap
  IntegralMixedAuxiliaryMarkedIntegerPlan.degree IntegralMixedAuxiliaryMarkedIntegerSource.source
  IntegralMixedAuxiliaryMarkedIntegerPlan.spatial

noncomputable def parentCommands :=paddedPast (defaultInstruction P PLAN r) ((PLAN).rules r)
  (beginBirth hn ht ha hR0 old)

include hv hd hE in
theorem parent_room :(parentCommands hn ht ha hR0 old left right side).length≤(P).cap r+1+1:=by
  rw [parentCommands,paddedPast_length,begin_eq_start hn ht ha hR0 old left right side]
  exact (IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 r j hj).trans (Nat.le_succ _)

noncomputable def parentState :=reframe (run (initial P PLAN r)
  (parentCommands hn ht ha hR0 old left right side)
  (parent_room hn ht ha hR0 old hv hd left right side hE)) (Q r)
    (IntegralMixedStaticRecordPrefix.cap (Q r) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r))

private theorem snapshot_commands_congr {a S B :ℕ} {V :SpatialSource a}
    (x :State V S B 0 (Fin 0)) (cs ds :List (Instruction a B))
    (hc :cs.length≤S+1) (hd :ds.length≤S+1) (hcs :cs=ds) :
    IntegralMixedPrefixSnapshot.ofCommands x cs hc=IntegralMixedPrefixSnapshot.ofCommands x ds hd:=by
  subst ds
  rfl

theorem snapshot_parent :IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 r j hj=
    IntegralMixedPrefixSnapshot.ofState (parentState hn ht ha hR0 old hv hd left right side hE):=by
  have HE :paddedPast (defaultInstruction P PLAN r) ((PLAN).rules r) (number n r+8+j)=
      parentCommands hn ht ha hR0 old left right side:=by
    unfold parentCommands
    rw [begin_eq_start hn ht ha hR0 old left right side]
  exact snapshot_commands_congr _ _ _ _ _ HE

theorem canonical_snapshot_parent :IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 c j cj=
    IntegralMixedPrefixSnapshot.ofState
      (IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he):=by
  change IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 c
    (IntegralMixedRoadmapRetainedAppend.start hn ht ha hR0 old) cj=_
  unfold IntegralMixedRoadmapRetainedAppend.parentState
  exact snapshot_commands_congr _ _ _ _ _
    (IntegralMixedRoadmapRetainedAppend.parent_commands hn ht ha hR0 old hv hd e he)

private theorem state_heq (a b :IntegralMixedPrefixSnapshot.Data) (h :a=b) :HEq a.state b.state:=by
  subst b
  rfl

theorem parent_snapshot_eq :
    IntegralMixedPrefixSnapshot.ofState (parentState hn ht ha hR0 old hv hd left right side hE)=
      IntegralMixedPrefixSnapshot.ofState
        (IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he):=by
  have HN:=prefix_snapshot hn ht ha hR0 old hv hd left right side hE j (Nat.le_refl _)
  have HC:=IntegralMixedRoadmapRetainedAppend.prefix_snapshot hn ht ha hR0 old hv hd e he j (Nat.le_refl _)
  have HS :IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 r j hj=
      IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 c j cj:=HN.trans HC.symm
  rw [snapshot_parent hn ht ha hR0 old hv hd left right side hE,
    canonical_snapshot_parent hn ht ha hR0 old hv hd] at HS
  exact HS

theorem parent_state_heq :HEq (parentState hn ht ha hR0 old hv hd left right side hE)
    (IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he):=
  state_heq _ _ (parent_snapshot_eq hn ht ha hR0 old hv hd left right side hE)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
