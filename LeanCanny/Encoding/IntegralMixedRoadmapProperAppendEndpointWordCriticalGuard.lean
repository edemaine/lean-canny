/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalEndpointPhysicalColumns
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendEndpointCriticalGuard
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendEndpointCriticalMetadata
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendEndpointWordCutGuard
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedNativeReadback
/-! # The sampled endpoint tuple supplies its actual selected physical value -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedFramedPhysicalIndex (arity prefixArity enumerate)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedFramedFixedContinuation (wrap)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "SAMP"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedPhysicalMarkedPlan.tables

private theorem native_selected_lt (root :List Bool) (b :ℕ)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (pair root []) b):
    prefixArity (BK).parameters T (pair ((BK).key (pair root [])) (List.replicate b true))+
      IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (pair root []) b<
        (SAMP).count (pair root []):=by
  have HL:=IntegralMixedFramedCriticalGuardBits.physical_lt (BK).parameters (BK).plan (BK).data T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false)
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (BK).key) IntegralFramedPhysicalCriticalGuardScan.stage
    (pair (pair root []) (List.replicate b true)) hb
  have HE:=IntegralMixedPhysicalGuardScan.count_eq hn ht ha (radius_binary hR0) false
    (pair root []) (List.replicate b true)
  simpa only [IntegralMixedFramedCriticalGuardBits.physical,IntegralMixedFramedCriticalGuardBits.packet,
    IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
    pairFst_pair,pairSnd_pair,List.length_replicate,IntegralMixedPhysicalPointCompanionScan.selected,
    Nat.add_assoc] using HL.trans_eq HE

private theorem natural_selected (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid SAMP (pair root []) w) (u :ℕ→ℝ)
    (HJ :IntegralMixedMarkedJointFieldReadback.Joint hn ht ha hR0 root w hw u)
    (b :ℕ) (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (pair root []) b):
    IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw
      (prefixArity (BK).parameters T (pair ((BK).key (pair root [])) (List.replicate b true))+
        IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (pair root []) b)=
      u (prefixArity (BK).parameters T (pair ((BK).key (pair root [])) (List.replicate b true))+
        IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (pair root []) b):=by
  let q:=prefixArity (BK).parameters T (pair ((BK).key (pair root [])) (List.replicate b true))+
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (pair root []) b
  have HC :q<(SAMP).count (pair root []):=native_selected_lt hn ht ha hR0 root b hb
  have HC' :q<IntegralFramedPhysicalSquare.count (BK).parameters (BK).plan ((BK).key (pair root [])):=HC
  have HN:=IntegralMixedRoadmapSeedResampling.seed_candidates hn ht ha hR0 (pair root []) w hw u HJ
  change IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw q=u q
  unfold IntegralMixedMarkedPrefixFieldReadback.natural IntegralFramedPhysicalSquare.naturalPoint
    IntegralMixedMarkedPrefixFieldReadback.context
  rw [dite_eq_left HC']
  exact HN ⟨q,HC⟩

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
local notation "js"=>R.orderedFree hk
local notation "K"=>List.length js
local notation "C"=>canonicalObservation hn ht ha hR0 old hv hd left right R side
local notation "finish"=>finishBirth hn ht ha hR0 old hv hd left right R side
local notation "birth" i=>endpointBirth hn ht ha hR0 old hv hd left right R i
local notation "raw" i=>endpointRawIndex hn ht ha hR0 old hv hd left right R i
local notation "CTX"=>IntegralMixedMarkedPrefixFieldReadback.context r

noncomputable local instance endpointWordCriticalIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs
attribute [local irreducible] IntegralMixedPhysicalFieldEquality.point IntegralMixedMarkedPrefixObservation.observation
  preparedRoot IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentState IntegralMixedRoadmapRetainedAppend.parentDescriptor
  IntegralMixedRoadmapRetainedAppend.parentTuple IntegralMixedRoadmapRetainedAppend.parentValues
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedAuxiliaryMarkedIntegerPlan.spatial IntegralMixedRoadmapProperParent.hom

local notation "Q0"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c
local notation "hQ0"=>IntegralMixedStaticRecordPrefix.cap Q0
  (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)

private theorem endpoint_physical_resources :
    (P).cap r=(P).cap c ∧(P).width r=(P).width c:=by
  have HC:IntegralMixedAuxiliaryMarkedIntegerSource.candidate r=IntegralMixedAuxiliaryMarkedIntegerSource.candidate c:=
    (prepared_candidate hn ht ha hR0 old R.leftSpec R.rightSpec side).trans
      (IntegralMixedRoadmapRetainedAppend.prepared_candidate hn ht ha hR0 old e).symm
  have HCount:IntegralMixedCausalRecordPlanBits.count r=IntegralMixedCausalRecordPlanBits.count c:=
    (prepared_count hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side
      (endpoints_good hn ht ha hR0 old hv hd left right R)).trans
      (IntegralMixedRoadmapRetainedAppend.prepared_count hn ht ha hR0 old hv hd e he).symm
  exact ⟨IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0 r c HC HCount,
    IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 r c HC⟩

private theorem endpoint_physical_birth (i :ℕ) (hi :i<R.result.commands.length):
    (birth i)=(oldCs).length+(R.result.commands.drop (i+1)).length:=by
  have HB:=(cutAt_birth (m:=(oldCs).length) R.result.commands i hi)
  have HP:=IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 old hv hd e he
  change (oldCs).length=beginBirth hn ht ha hR0 old at HP
  unfold endpointBirth
  omega

private theorem endpoint_physical_power (i :ℕ) (hi :i<R.result.commands.length):
    UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) (birth i)=
      UniformIntegralPowerSchedule.physical ((P).cap c+1) (2^(P).width c)
        ((oldCs).length+(R.result.commands.drop (i+1)).length):=by
  rw [(endpoint_physical_resources hn ht ha hR0 old hv hd left right R side).1,
    (endpoint_physical_resources hn ht ha hR0 old hv hd left right R side).2,
    endpoint_physical_birth hn ht ha hR0 old hv hd left right R i hi]

private theorem command_critical_exists {a BW :ℕ} {V :SpatialSource a}
    (cmd :IntegralMixedFullHistoryScript.Command V BW) (h :cmd.isCritical=true):
    ∃rule,cmd=.critical rule:=by
  cases cmd with
  | integer=>cases h
  | critical rule=>exact ⟨rule,rfl⟩
  | cut=>cases h

private theorem endpoint_partial_arity (i :ℕ):
    arity (endpointPartialCommands hn ht ha hR0 old hv hd left right R i)=
      arity (List.append (α:=Instruction ((P).ambient c) ((P).width c))
        ((R.result.commands.drop (i+1)).map (wrap Q0 hQ0)) oldCs):=by
  unfold endpointPartialCommands canonicalEndpointWrap
  rfl

theorem WordReceipt.endpoint_native_power {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (layout :R.levelIndex hk g (IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd) side≃Fin (C).arity)
    (hLayout :HEq (enumerate (canonicalCompiledProgram hn ht ha hR0 old hv hd left right R side)) layout)
    (hPair :∀p :IntegralMixedFullHistoryScript.Index (Index (Fin 0) oldCs) R.result.commands,
      u (layout (R.levelPairColumn hk g
        (IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd) side p)).val=R.result.tuple p)
    (i :ℕ) (hi :i<R.result.commands.length)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false CTX (birth i)):
    endpointNativePower hn ht ha hR0 r W.word W.valid (birth i)=
      endpointPhysicalValue hn ht ha hR0 old hv hd left right R i hi:=by
  let hg:=IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
  obtain ⟨rule,HC⟩:=command_critical_exists R.result.commands[i]
    (endpoint_critical_tag hn ht ha hR0 old hv hd left right R side i hi hb)
  let p:=criticalAtColumn oldCs R.result.commands i hi rule HC (criticalCoordinate rule)
  let q:=arity (endpointPartialCommands hn ht ha hR0 old hv hd left right R i)+(criticalCoordinate rule).val
  have HNumber :(layout (R.levelPairColumn hk g hg side p)).val=q:=by
    dsimp only [p,q]
    rw [endpoint_partial_arity hn ht ha hR0 old hv hd left right R i]
    exact R.level_endpoint_critical_number hQ0 oldCs hk g hg side layout hLayout i hi rule HC (criticalCoordinate rule)
  have HRaw :W.tuple q=R.result.tuple p:=
    (congrArg W.tuple HNumber).symm.trans
      ((W.preserved _ (layout (R.levelPairColumn hk g hg side p)).isLt).trans (hPair p))
  have HIndex :prefixArity (BK).parameters T (pair ((BK).key CTX) (List.replicate (birth i) true))+
      IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false CTX (birth i)=q:=by
    rw [endpoint_prefix_arity hn ht ha hR0 old hv hd left right R side i hi,
      endpoint_selected_critical hn ht ha hR0 old hv hd left right R side i hi rule HC]
    rfl
  have HJ :IntegralMixedMarkedJointFieldReadback.Joint hn ht ha hR0 r W.word W.valid W.tuple:=W.joint
  have HNat:=natural_selected hn ht ha hR0 r W.word W.valid W.tuple HJ (birth i) hb
  have HIndexPair:=HIndex
  unfold IntegralMixedMarkedPrefixFieldReadback.context at HIndexPair
  rw [HIndexPair] at HNat
  have HP:=selectedPhysical_at_column oldCs x R.result.commands R.result.room R.result.tuple i hi rule HC
  change endpointPhysicalValue hn ht ha hR0 old hv hd left right R i hi=
    R.result.tuple p^UniformIntegralPowerSchedule.physical ((P).cap c+1) (2^(P).width c)
      ((oldCs).length+(R.result.commands.drop (i+1)).length) at HP
  have HNative :UniformIntegralPowerSchedule.physical ((BK).parameters.cap r+1)
      (2^(BK).parameters.width r) (birth i)=
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) (birth i):=by
    unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank
    rfl
  unfold endpointNativePower
  rw [HIndex,HNat,HRaw,HNative,endpoint_physical_power hn ht ha hR0 old hv hd left right R side i hi]
  exact HP.symm

theorem WordReceipt.endpoint_native_critical_guard {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (layout :R.levelIndex hk g (IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd) side≃Fin (C).arity)
    (hLayout :HEq (enumerate (canonicalCompiledProgram hn ht ha hR0 old hv hd left right R side)) layout)
    (hPair :∀p :IntegralMixedFullHistoryScript.Index (Index (Fin 0) oldCs) R.result.commands,
      u (layout (R.levelPairColumn hk g
        (IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd) side p)).val=R.result.tuple p)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀j :Fin ((oldCs).length+R.result.commands.length+1+K+1+K),
      (C).point u j.val=IntegralMixedChronologicalLevelScalarValues.levelValues
        pMID pChild R.result.nextValues g js j)
    (GG :EndpointGuarded hn ht ha hR0 old hv hd left right R)
    (i :ℕ) (hi :i<R.result.commands.length)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false CTX (birth i)):
    IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false CTX W.word W.valid (birth i) hb=
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false CTX W.word W.valid (birth i)
        ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false CTX (birth i),
          IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false CTX (birth i) hb⟩:=
  endpoint_critical_guard hn ht ha hR0 old hv hd left right R side GG W.word W.valid i hi hb
    (W.endpoint_new_value hn ht ha hR0 old hv hd left right R side pMID pChild hValues GG i hi)
    (W.endpoint_native_power hn ht ha hR0 old hv hd left right R side layout hLayout hPair i hi hb)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
