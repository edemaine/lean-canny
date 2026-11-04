/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendEndpointCutGuard
public import LeanCanny.Geometry.IntegralMixedGuardedProgramCriticalAt
public import LeanCanny.Encoding.IntegralMixedMarkedCriticalNatural
/-! # Constructed critical endpoints satisfy their actual own-word native guards -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedOptionalEndpoints
open IntegralMixedChronologicalEndpoint IntegralMixedChosenLocalRealization UniformIntegralPowerSchedule
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "PLAN"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "FAM"=>IntegralMixedFramedHistoryFamilyBits.family P PLAN H
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "SAMP"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" root=>IntegralMixedMarkedPrefixFieldReadback.context root

private theorem instruction_isCritical_heq {a b W V :ℕ}
    (u :Instruction a W) (v :Instruction b V) (hn :a=b) (hB :W=V) (he :HEq u v):
    u.command.isCritical=v.command.isCritical:=by
  subst b
  subst V
  cases eq_of_heq he
  rfl

private noncomputable def instructionCritical (P0 :Parameters)
    (D0 :IntegralMixedFramedHistoryFamilyBits.Plan P0) (root :List Bool) (b :ℕ):Bool:=
  (IntegralMixedFramedRootPullback.instructionAt P0 D0 root b).command.isCritical

noncomputable def endpointNativePower (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid SAMP (CTX root) w) (b :ℕ):ℝ:=
  IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw
    (IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX root)) (List.replicate b true))+
      IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX root) b)^
    UniformIntegralPowerSchedule.physical ((P).cap root+1) (2^(P).width root) b

variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he
local notation "z"=>IntegralMixedRoadmapRetainedAppend.parentTuple hn ht ha hR0 old hv hd e he
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd e he
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "birth" i=>endpointBirth hn ht ha hR0 old hv hd left right R i
local notation "raw" i=>endpointRawIndex hn ht ha hR0 old hv hd left right R i

noncomputable local instance endpointCriticalParentFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedPhysicalFieldEquality.point
  IntegralMixedMarkedPrefixObservation.observation IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentState IntegralMixedRoadmapRetainedAppend.parentTuple
  IntegralMixedRoadmapRetainedAppend.parentValues IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedAuxiliaryMarkedIntegerPlan.spatial IntegralMixedAuxiliaryMarkedIntegerPlan.degree
  IntegralMixedRoadmapProperParent.hom

private theorem critical_endpoint_candidate :
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate r=IntegralMixedAuxiliaryMarkedIntegerSource.candidate c:=
  (prepared_candidate hn ht ha hR0 old R.leftSpec R.rightSpec side).trans
    (IntegralMixedRoadmapRetainedAppend.prepared_candidate hn ht ha hR0 old e).symm

private theorem critical_endpoint_initial_canonical :Canonical x:=by
  unfold IntegralMixedRoadmapRetainedAppend.parentState
  apply IntegralMixedFramedHistoryScript.reframe_canonical
  apply IntegralMixedFramedHistoryScript.run_canonical
  intro i
  exact Fin.elim0 i

theorem endpoint_critical_tag (i :ℕ) (hi :i<R.result.commands.length)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX r) (birth i)):
    R.result.commands[i].isCritical=true:=by
  obtain ⟨rule,HC⟩:=IntegralMixedFramedCriticalGuardBits.active_critical P PLAN H T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false)
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
    (pair (CTX r) (List.replicate (birth i) true)) hb
  have HA :(IntegralMixedFramedRootPullback.instructionAt P PLAN
      (pairFst (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key
        (pair (CTX r) (List.replicate (birth i) true))))
      (IntegralFramedPhysicalCriticalGuardScan.stage (pair (CTX r) (List.replicate (birth i) true)))).command.isCritical=true:=by
    rw [HC]
    rfl
  change instructionCritical P PLAN _ _=true at HA
  simp only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
    pairFst_pair,pairSnd_pair,List.length_replicate] at HA
  have HR :pairFst ((B).key (CTX r))=r:=by
    rw [IntegralMixedPhysicalFieldEquality.key_root]
    exact pairFst_pair _ _
  rw [HR] at HA
  have HE:=endpoint_instruction hn ht ha hR0 old hv hd left right R side i hi
  have HTag:=instruction_isCritical_heq _ _
    (IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 r c
      (critical_endpoint_candidate hn ht ha hR0 old hv hd left right R side))
    (IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 r c
      (critical_endpoint_candidate hn ht ha hR0 old hv hd left right R side)) HE
  change (IntegralMixedFramedRootPullback.instructionAt
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0))
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)) r (birth i)).command.isCritical=
    R.result.commands[i].isCritical at HTag
  unfold instructionCritical IntegralMixedPhysicalMarkedPlan.bank at HA
  exact HTag.symm.trans HA

noncomputable def endpointPhysicalValue (i :ℕ) (hi :i<R.result.commands.length):ℝ:=
  selectedPhysical (endpointBeforeState hn ht ha hR0 old hv hd left right R i)
    (cutAt_fit R.result.commands R.result.room i hi) R.result.commands[i]
    (cutAtTuple R.result.commands i hi R.result.tuple)

private theorem endpoint_constructed_correlation
    (GG :EndpointGuarded hn ht ha hR0 old hv hd left right R)
    (i :ℕ) (hi :i<R.result.commands.length) (hc :R.result.commands[i].isCritical=true):
    endpointNewValue hn ht ha hR0 old hv hd left right R i hi=
      endpointPhysicalValue hn ht ha hR0 old hv hd left right R i hi:=
  GuardedProgram.critical_at GG (critical_endpoint_initial_canonical hn ht ha hR0 old hv hd)
    (IntegralMixedRoadmapProperParent.hom_generators hn ht ha hR0 old hv hd) i hi hc

theorem endpoint_critical_scalarValue
    (GG :EndpointGuarded hn ht ha hR0 old hv hd left right R)
    (w :List Bool) (hw :SquareSampleCompleteVertices.Valid SAMP (CTX r) w)
    (i :ℕ) (hi :i<R.result.commands.length)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX r) (birth i))
    (hHead :IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX r) w hw (birth i)=
      endpointNewValue hn ht ha hR0 old hv hd left right R i hi)
    (hPhysical :endpointNativePower hn ht ha hR0 r w hw (birth i)=
      endpointPhysicalValue hn ht ha hR0 old hv hd left right R i hi):
    IntegralMixedPhysicalPointCompanionScan.scalarValue hn ht ha (radius_binary hR0) false (CTX r) w (birth i)=
      InfinitesimalSign.encode 0:=by
  apply (IntegralMixedMarkedCriticalNatural.scalarValue_zero_iff hn ht ha hR0 r w hw (birth i) hb).mpr
  exact hHead.trans ((endpoint_constructed_correlation hn ht ha hR0 old hv hd left right R GG i hi
    (endpoint_critical_tag hn ht ha hR0 old hv hd left right R side i hi hb)).trans hPhysical.symm)

theorem endpoint_critical_guard
    (GG :EndpointGuarded hn ht ha hR0 old hv hd left right R)
    (w :List Bool) (hw :SquareSampleCompleteVertices.Valid SAMP (CTX r) w)
    (i :ℕ) (hi :i<R.result.commands.length)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX r) (birth i))
    (hHead :IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX r) w hw (birth i)=
      endpointNewValue hn ht ha hR0 old hv hd left right R i hi)
    (hPhysical :endpointNativePower hn ht ha hR0 r w hw (birth i)=
      endpointPhysicalValue hn ht ha hR0 old hv hd left right R i hi):
    IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false (CTX r) w hw (birth i) hb=
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false (CTX r) w hw (birth i)
        ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX r) (birth i),
          IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false (CTX r) (birth i) hb⟩:=
  (IntegralMixedPhysicalPointCompanionScan.scalarValue_zero_iff hn ht ha (radius_binary hR0) false
    (CTX r) w hw (birth i) hb).mp
      (endpoint_critical_scalarValue hn ht ha hR0 old hv hd left right R side GG w hw i hi hb hHead hPhysical)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
