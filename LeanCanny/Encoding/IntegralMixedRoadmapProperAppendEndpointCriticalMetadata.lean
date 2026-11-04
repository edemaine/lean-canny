/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendEndpointCriticalGuard
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalLayout
/-! # Exact native physical columns and selected coordinates at endpoint births -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalEndpoint
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem endpoint_arity_heq {a b W V :ℕ} (cs :List (Instruction a W)) (ds :List (Instruction b V))
    (hn :a=b) (hB :W=V) (he :HEq cs ds):
    IntegralMixedFramedPhysicalIndex.arity cs=IntegralMixedFramedPhysicalIndex.arity ds:=by
  subst b
  subst V
  cases eq_of_heq he
  rfl

private theorem endpoint_header_heq {a b W V :ℕ} (u :Instruction a W) (v :Instruction b V)
    (hn :a=b) (hB :W=V) (he :HEq u v):
    IntegralMixedCommandHeaderBits.command u.command=IntegralMixedCommandHeaderBits.command v.command:=by
  subst b
  subst V
  cases eq_of_heq he
  rfl

private noncomputable def endpointHeaderAt (A :Parameters) (D :IntegralMixedFramedHistoryFamilyBits.Plan A)
    (root :List Bool) (b :ℕ):IntegralMixedCommandHeaderBits.Header:=
  IntegralMixedCommandHeaderBits.command (IntegralMixedFramedRootPullback.instructionAt A D root b).command

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "PLAN"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "PC"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "CTX"=>IntegralMixedMarkedPrefixFieldReadback.context r
local notation "b" i=>endpointBirth hn ht ha hR0 old hv hd left right R i

noncomputable local instance endpointCriticalMetadataIndexFintype :Fintype (Index (Fin 0) oldCs):=
  indexFintype (Fin 0) oldCs
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedPhysicalMarkedPlan.tables IntegralMixedFramedHistoryFamilyBits.family
  preparedRoot IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentState IntegralMixedRoadmapRetainedAppend.parentDescriptor
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus

private theorem endpoint_metadata_candidate :IntegralMixedAuxiliaryMarkedIntegerSource.candidate r=
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate c:=
  (prepared_candidate hn ht ha hR0 old R.leftSpec R.rightSpec side).trans
    (IntegralMixedRoadmapRetainedAppend.prepared_candidate hn ht ha hR0 old e).symm

private theorem endpoint_metadata_ambient :(P).ambient r=(PC).ambient c:=by
  unfold IntegralMixedPhysicalMarkedPlan.bank
  exact IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 r c
    (endpoint_metadata_candidate hn ht ha hR0 old hv hd left right R side)

private theorem endpoint_metadata_width :(P).width r=(PC).width c:=by
  unfold IntegralMixedPhysicalMarkedPlan.bank
  exact IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 r c
    (endpoint_metadata_candidate hn ht ha hR0 old hv hd left right R side)

private theorem endpoint_metadata_root :pairFst ((B).key CTX)=r:=by
  rw [IntegralMixedPhysicalFieldEquality.key_root hn ht ha (radius_binary hR0)]
  exact pairFst_pair _ _

theorem endpoint_prefix_arity (i :ℕ) (hi :i<R.result.commands.length) :
    IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key CTX) (List.replicate (b i) true))=
      IntegralMixedFramedPhysicalIndex.arity (endpointPartialCommands hn ht ha hR0 old hv hd left right R i):=by
  rw [IntegralMixedFramedPhysicalIndex.prefixArity_packet P PLAN H T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false),
    endpoint_metadata_root hn ht ha hR0 old hv hd left right R side]
  have HP:HEq (paddedPast (defaultInstruction P PLAN r) ((PLAN).rules r) (b i))
      (endpointPartialCommands hn ht ha hR0 old hv hd left right R i):=by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    exact endpoint_prefix_commands hn ht ha hR0 old hv hd left right R side i hi
  exact endpoint_arity_heq _ _
    (endpoint_metadata_ambient hn ht ha hR0 old hv hd left right R side)
    (endpoint_metadata_width hn ht ha hR0 old hv hd left right R side) HP

theorem endpoint_native_header (i :ℕ) (hi :i<R.result.commands.length) :
    IntegralMixedFramedCriticalGuardBits.header T (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key)
      IntegralFramedPhysicalCriticalGuardScan.stage (pair CTX (List.replicate (b i) true))=
      IntegralMixedCommandHeaderBits.command R.result.commands[i]:=by
  have HA:=IntegralMixedFramedCriticalGuardBits.header_actual P PLAN H T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false)
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
    (pair CTX (List.replicate (b i) true))
  change _=endpointHeaderAt P PLAN _ _ at HA
  simp only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
    pairFst_pair,pairSnd_pair,List.length_replicate] at HA
  rw [endpoint_metadata_root hn ht ha hR0 old hv hd left right R side] at HA
  have HI:HEq (IntegralMixedFramedRootPullback.instructionAt P PLAN r (b i))
      (canonicalEndpointWrap hn ht ha hR0 old R.result.commands[i]):=by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    exact endpoint_instruction hn ht ha hR0 old hv hd left right R side i hi
  have HH:=endpoint_header_heq _ _
    (endpoint_metadata_ambient hn ht ha hR0 old hv hd left right R side)
    (endpoint_metadata_width hn ht ha hR0 old hv hd left right R side) HI
  exact HA.trans HH

theorem endpoint_selected (i :ℕ) (hi :i<R.result.commands.length) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false CTX (b i)=
      (IntegralMixedCommandHeaderBits.command R.result.commands[i]).offset+
        (IntegralMixedCommandHeaderBits.command R.result.commands[i]).coordinate:=by
  unfold IntegralMixedPhysicalPointCompanionScan.selected
  rw [endpoint_native_header hn ht ha hR0 old hv hd left right R side i hi]

theorem endpoint_selected_critical (i :ℕ) (hi :i<R.result.commands.length)
    (rule :CriticalRule ((PC).ambient c)) (hc :R.result.commands[i]=.critical rule) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false CTX (b i)=
      rule.offset.val+rule.coordinate%((PC).ambient c-rule.offset.val+1):=by
  have HH:=congrArg (fun cmd=>
    (IntegralMixedCommandHeaderBits.command cmd).offset+(IntegralMixedCommandHeaderBits.command cmd).coordinate) hc
  exact (endpoint_selected hn ht ha hR0 old hv hd left right R side i hi).trans HH

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
