/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendParentTransfer
/-! # The actual parent commands keep the canonical typed physical enumeration -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex IntegralMixedCausalRecordBits
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem commands_prefix_heq {n m S T B C :ℕ} {V :SpatialSource n} {W :SpatialSource m}
    (x :State V S B 0 (Fin 0)) (y :State W T C 0 (Fin 0))
    (rs :List (Record n B)) (ds :List (Record m C)) (hr :rs.length≤S+1) (hd :ds.length≤T+1)
    (fr :Instruction n B) (fd :Instruction m C) (a b :ℕ) (ha :a≤rs.length) (hb :b≤ds.length)
    (en :n=m) (eS :S=T) (eB :B=C) (ea :a=b) (eV :HEq V W) (ex :HEq x y)
    (ep :HEq (rs.reverse.take a) (ds.reverse.take b)) :
    HEq (paddedPast fr (IntegralMixedCausalPlanBits.commands x rs hr) a)
      (paddedPast fd (IntegralMixedCausalPlanBits.commands y ds hd) b):=by
  subst m
  subst T
  subst C
  subst b
  cases eq_of_heq eV
  cases eq_of_heq ex
  exact heq_of_eq (IntegralMixedCausalPrefixCongruence.prefix_eq x rs ds hr hd fr fd a ha hb (eq_of_heq ep))

private theorem command_layout_heq {a b B C :ℕ} (ha :a=b) (hB :B=C)
    (cs :List (Instruction a B)) (ds :List (Instruction b C)) (hcs :HEq cs ds) :
    Index (Fin 0) cs=Index (Fin 0) ds ∧ arity cs=arity ds ∧ HEq (enumerate cs) (enumerate ds):=by
  subst b
  subst C
  cases eq_of_heq hcs
  exact ⟨rfl,rfl,HEq.rfl⟩

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (left right :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old left right)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "r"=>preparedRoot hn ht ha hR0 old left right side
local notation "j"=>start hn ht ha hR0 old
local notation "hj"=>prepared_start_fit hn ht ha hR0 old hv hd left right side hE
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "newCs"=>parentCommands hn ht ha hR0 old left right side
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank preparedRoot
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedAuxiliaryMarkedIntegerPlan.degree IntegralMixedAuxiliaryMarkedIntegerSource.source
  IntegralMixedAuxiliaryMarkedIntegerPlan.spatial IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedExceptionalBounds.auxiliaryCap

include hE in
theorem parent_commands_heq :HEq newCs oldCs:=by
  have HC:IntegralMixedAuxiliaryMarkedIntegerSource.candidate r=
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate c:=
    (prepared_candidate hn ht ha hR0 old left right side).trans
      (IntegralMixedRoadmapRetainedAppend.prepared_candidate hn ht ha hR0 old e).symm
  have HCount:IntegralMixedCausalRecordPlanBits.count r=IntegralMixedCausalRecordPlanBits.count c:=
    (prepared_count hn ht ha hR0 old hv hd left right side hE).trans
      (IntegralMixedRoadmapRetainedAppend.prepared_count hn ht ha hR0 old hv hd e he).symm
  have HCode:∀i,i<j→IntegralMixedCausalRecordPlanBits.code r i=IntegralMixedCausalRecordPlanBits.code c i:=by
    intro i hi
    exact (prepared_record hn ht ha hR0 old hv left right side i hi).trans
      (IntegralMixedRoadmapRetainedAppend.prepared_record hn ht ha hR0 old hv e i hi).symm
  have HN:=IntegralMixedMarkedPreludeCongruence.number_eq (n:=n) r c HC
  have HFit:=hj
  have HPrefix:=commands_prefix_heq (initial P PLAN r) (initial P PLAN c)
    (IntegralMixedMarkedPrefixRecords.records hn ht ha hR0 r)
    (IntegralMixedMarkedPrefixRecords.records hn ht ha hR0 c)
    (IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 r)
    (IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 c)
    (defaultInstruction P PLAN r) (defaultInstruction P PLAN c)
    (number n r+8+j) (number n c+8+j)
    (by rw [IntegralMixedMarkedPrefixRecords.length];omega)
    (by rw [IntegralMixedMarkedPrefixRecords.length];omega)
    (IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 r c HC)
    (congrArg (·+1) (IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0 r c HC HCount))
    (IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 r c HC)
    (congrArg (fun k=>k+8+j) HN)
    (IntegralMixedMarkedPrefixRecords.source_heq (n:=n) (t:=t) (R0:=R0) r c HC)
    (IntegralMixedMarkedPrefixRecords.initial_heq hn ht ha hR0 r c HC HCount)
    (IntegralMixedMarkedPrefixRecords.prefix_heq hn ht ha hR0 r c HC HCount j hj HCode)
  rw [←IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 r,
    ←IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 c] at HPrefix
  have HOld :paddedPast (defaultInstruction P PLAN c) ((PLAN).rules c) (number n c+8+j)=oldCs:=
    IntegralMixedRoadmapRetainedAppend.parent_commands hn ht ha hR0 old hv hd e he
  rw [HOld] at HPrefix
  have HNew :paddedPast (defaultInstruction P PLAN r) ((PLAN).rules r) (number n r+8+j)=newCs:=by
    unfold parentCommands
    rw [begin_eq_start]
  rw [HNew] at HPrefix
  exact HPrefix

include hE in
theorem parent_layout :Index (Fin 0) newCs=Index (Fin 0) oldCs ∧
    arity newCs=arity oldCs ∧ HEq (enumerate newCs) (enumerate oldCs):=by
  have HC:IntegralMixedAuxiliaryMarkedIntegerSource.candidate r=
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate c:=
    (prepared_candidate hn ht ha hR0 old left right side).trans
      (IntegralMixedRoadmapRetainedAppend.prepared_candidate hn ht ha hR0 old e).symm
  exact command_layout_heq (IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 r c HC)
    (IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 r c HC) newCs oldCs
    (parent_commands_heq hn ht ha hR0 old hv hd left right side hE)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
