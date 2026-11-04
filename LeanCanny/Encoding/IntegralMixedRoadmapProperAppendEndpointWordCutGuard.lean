/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendEndpointCutGuard
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLevelFields
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixChronologicalField
public import LeanCanny.Geometry.IntegralMixedGuardedProgramCutValues
/-! # The sampled canonical word discharges endpoint cut numerical readbacks -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedChronologicalLevelScalarValues
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "SAMP"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false


variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "m"=>List.length oldCs+List.length R.result.commands
local notation "js"=>R.orderedFree hk
local notation "K"=>List.length js
local notation "C"=>canonicalObservation hn ht ha hR0 old hv hd left right R side
local notation "finish"=>finishBirth hn ht ha hR0 old hv hd left right R side
local notation "birth" i=>endpointBirth hn ht ha hR0 old hv hd left right R i
local notation "raw" i=>endpointRawIndex hn ht ha hR0 old hv hd left right R i
local notation "CTX"=>IntegralMixedMarkedPrefixFieldReadback.context r

noncomputable local instance endpointWordCutGuardIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedPhysicalFieldEquality.point IntegralMixedMarkedPrefixObservation.observation
  preparedRoot IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentState IntegralMixedRoadmapRetainedAppend.parentDescriptor
  IntegralMixedRoadmapRetainedAppend.parentTuple IntegralMixedRoadmapRetainedAppend.parentValues
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedAuxiliaryMarkedIntegerPlan.spatial IntegralMixedRoadmapProperParent.hom

private theorem endpoint_values_initial_canonical :Canonical x:=by
  unfold IntegralMixedRoadmapRetainedAppend.parentState
  apply IntegralMixedFramedHistoryScript.reframe_canonical
  apply IntegralMixedFramedHistoryScript.run_canonical
  intro i
  exact Fin.elim0 i

theorem endpoint_program_values (GG :EndpointGuarded hn ht ha hR0 old hv hd left right R)
    (i :ℕ) (hi :i<R.result.commands.length) :
    CutAtValues x R.result.commands R.result.room R.result.tuple R.result.nextValues i hi:=
  GuardedProgram.cut_at_values GG (endpoint_values_initial_canonical hn ht ha hR0 old hv hd)
    (IntegralMixedRoadmapProperParent.hom_generators hn ht ha hR0 old hv hd)
    (IntegralMixedRoadmapProperParent.hom_values hn ht ha hR0 old hv hd) i hi

theorem WordReceipt.endpoint_field_at {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀j :Fin (m+1+K+1+K),(C).point z j.val=levelValues pMID pChild R.result.nextValues g js j)
    (k :Fin m) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX W.word W.valid
      (beginBirth hn ht ha hR0 old+R.result.commands.length-1-k.val)=R.result.nextValues k:=by
  have HW:=W.endpoint_field hn ht ha hR0 old hv hd left right R side pMID pChild hValues k
  have HF:finish=beginBirth hn ht ha hR0 old+R.result.commands.length+2+2*K:=by
    unfold finishBirth
    rw [R.levelCodes_length]
    omega
  have HE:finish-1-(K+1+(K+1+k.val))=beginBirth hn ht ha hR0 old+R.result.commands.length-1-k.val:=by omega
  exact (congrArg (IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX W.word W.valid) HE).symm.trans HW

theorem WordReceipt.endpoint_new_value {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀j :Fin (m+1+K+1+K),(C).point z j.val=levelValues pMID pChild R.result.nextValues g js j)
    (GG :EndpointGuarded hn ht ha hR0 old hv hd left right R) (i :ℕ) (hi :i<R.result.commands.length) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX W.word W.valid (birth i)=
      endpointNewValue hn ht ha hR0 old hv hd left right R i hi:=by
  have HG:=(endpoint_program_values hn ht ha hR0 old hv hd left right R GG i hi).1
  have HW:=W.endpoint_field_at hn ht ha hR0 old hv hd left right R side pMID pChild hValues
    (cutAtHeadIndex (oldCs).length R.result.commands i hi)
  exact HW.trans HG.symm

private theorem endpoint_before_birth (i :ℕ) (hi :i<R.result.commands.length) :
    (oldCs).length+(R.result.commands.drop (i+1)).length=birth i:=by
  have HB:(oldCs).length+(R.result.commands.drop (i+1)).length=
      (oldCs).length+R.result.commands.length-1-i:=cutAt_birth R.result.commands i hi
  have HP:=IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 old hv hd e he
  change (oldCs).length=beginBirth hn ht ha hR0 old at HP
  unfold endpointBirth
  omega

private theorem endpoint_extend_finite {k :ℕ} (f :Fin k→ℝ) (i :Fin k) :
    IntegralMixedFramedBankObservation.extend f i.val=f i:=by
  simp only [IntegralMixedFramedBankObservation.extend,dite_eq_left i.isLt]

theorem WordReceipt.endpoint_before_values {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀j :Fin (m+1+K+1+K),(C).point z j.val=levelValues pMID pChild R.result.nextValues g js j)
    (GG :EndpointGuarded hn ht ha hR0 old hv hd left right R) (i :ℕ) (hi :i<R.result.commands.length)
    (k :ℕ) (hkb :k<birth i) :
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 r (raw i)
      (endpoint_raw_lt hn ht ha hR0 old hv hd left right R side i hi).le).point
      (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r W.word W.valid) k=
      endpointBeforeValues hn ht ha hR0 old hv hd left right R i hi k:=by
  have HB:=endpoint_before_birth hn ht ha hR0 old hv hd left right R i hi
  let j :Fin ((oldCs).length+(R.result.commands.drop (i+1)).length):=⟨k,by omega⟩
  let idx:=cutAtBeforeIndex (oldCs).length R.result.commands i hi j
  have HG:=(endpoint_program_values hn ht ha hR0 old hv hd left right R GG i hi).2 j
  have HCan:endpointBeforeValues hn ht ha hR0 old hv hd left right R i hi k=R.result.nextValues idx:=by
    change IntegralMixedFramedBankObservation.extend
      (IntegralMixedFullBankPoint.point (endpointBeforeState hn ht ha hR0 old hv hd left right R i)
        (cutAtTuple R.result.commands i hi R.result.tuple∘IntegralMixedChosenLocalRealization.oldColumn R.result.commands[i])) k=_
    exact (endpoint_extend_finite _ j).trans HG
  have HW:=W.endpoint_field_at hn ht ha hR0 old hv hd left right R side pMID pChild hValues idx
  have HE:=endpoint_birth_eq hn ht ha hR0 old hv hd left right R side i hi
  have HP:=IntegralMixedMarkedPrefixChronologicalField.value hn ht ha hR0 r W.word W.valid (raw i)
    (endpoint_raw_lt hn ht ha hR0 old hv hd left right R side i hi).le k (hkb.trans_eq HE)
  have HClock:number n r+8+(raw i)-1-k=beginBirth hn ht ha hR0 old+R.result.commands.length-1-idx.val:=by
    dsimp only [idx,cutAtBeforeIndex,j]
    unfold endpointBirth at HE
    omega
  exact HP.trans ((congrArg (IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX W.word W.valid)
    HClock).trans HW) |>.trans HCan.symm

theorem WordReceipt.endpoint_native_cut_guard {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀j :Fin (m+1+K+1+K),(C).point z j.val=levelValues pMID pChild R.result.nextValues g js j)
    (GG :EndpointGuarded hn ht ha hR0 old hv hd left right R) (i :ℕ) (hi :i<R.result.commands.length)
    (hc :IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha (radius_binary hR0) false
      (IntegralFramedTraceCutScan.stagePacket (pair r W.word) (birth i))) :
    IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha (radius_binary hR0) false
      (IntegralFramedTraceCutScan.stagePacket (pair r W.word) (birth i)):=
  endpoint_cut_guard hn ht ha hR0 old hv hd left right R side GG W.word W.valid i hi
    (W.endpoint_before_values hn ht ha hR0 old hv hd left right R side pMID pChild hValues GG i hi)
    (W.endpoint_new_value hn ht ha hR0 old hv hd left right R side pMID pChild hValues GG i hi) hc

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
