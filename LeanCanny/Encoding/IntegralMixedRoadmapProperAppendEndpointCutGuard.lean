/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendEndpointSnapshot
public import LeanCanny.Encoding.IntegralMixedMarkedCutReceiptComplete
/-! # Constructed endpoint receipts give actual own-word native cut guards

The two numerical readbacks are explicit intermediate contracts. Creating
snapshots, commands, parent canonicality and generator identities are derived.
-/
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
local notation "SAMP"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" root=>IntegralMixedMarkedPrefixFieldReadback.context root

private theorem endpoint_saved_instruction (root :List Bool) (b :ℕ)
    (hb :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root) :
    HEq (IntegralMixedFramedHistoryFamilyBits.instruction P PLAN
      (IntegralMixedMarkedCutStage.saved hn ht ha hR0 root b))
      (IntegralMixedFramedRootPullback.instructionAt P PLAN root b):=by
  let key:=IntegralMixedMarkedCutStage.saved hn ht ha hR0 root b
  have HR :pairFst key=root:=
    (congrArg pairFst (IntegralMixedMarkedCutStage.saved_eq hn ht ha hR0 root b hb)).trans
      (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
  have HP :IntegralMixedFramedHistoryFamilyBits.prefixLength P key=b:=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P PLAN H key).symm.trans
      (IntegralMixedMarkedCutStage.saved_birth hn ht ha hR0 root b hb)
  exact IntegralMixedFramedRootPullback.instructionAt_congr P PLAN _ root _ b HR HP

private theorem endpoint_stageCut_iff (root w :List Bool) (b :ℕ) :
    IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha (radius_binary hR0) false
      (IntegralFramedTraceCutScan.stagePacket (pair root w) b)↔
    IntegralFramedCreatingCut.ParentCut P PLAN (IntegralMixedMarkedCutStage.parent hn ht ha hR0 root b):=by
  change IntegralFramedCreatingCut.ParentCut P PLAN
    (IntegralFramedTraceCutGuards.parent P (IntegralFramedTraceCutScan.stagePacket (pair root w) b))↔_
  have HE:=IntegralMixedPhysicalCutCoefficientSemantics.parent_packet hn ht ha (radius_binary hR0) false root w
    (List.replicate b true)
  simpa only [IntegralFramedTraceCutScan.stagePacket,IntegralMixedPhysicalCutCoefficientSemantics.stage,
    IntegralMixedMarkedCutStage.parent,pairFst_pair,pairSnd_pair] using
      Iff.of_eq (congrArg (IntegralFramedCreatingCut.ParentCut P PLAN) HE)

private theorem endpoint_family_receipt_transport (P0 :Parameters)
    (D0 :IntegralMixedFramedHistoryFamilyBits.Plan P0) (H0 :IntegralMixedFramedHistoryFamilyBits.Data P0 D0)
    (key :List Bool) (d :IntegralMixedPrefixSnapshot.Data) (hm :d.birth≤d.horizon)
    (cmd :IntegralMixedFullHistoryScript.Command d.source d.width)
    (hs :IntegralMixedPrefixSnapshot.ofState ((IntegralMixedFramedHistoryFamilyBits.family P0 D0 H0).state key)=d)
    (hc :HEq (IntegralMixedFramedHistoryFamilyBits.instruction P0 D0 key).command cmd)
    (values other :ℕ→ℝ) (a :ℝ)
    (hv :∀i<(IntegralMixedFramedHistoryFamilyBits.family P0 D0 H0).birth key,values i=other i) :
    IntegralMixedPrefixSnapshot.familyCutReceipt P0 D0 H0 key values a↔d.CutReceipt hm cmd other a:=
  IntegralMixedPrefixSnapshot.Data.cutReceipt_transport _ _ _ _ _ _ hs hc values other a hv

private theorem endpoint_receipt_head_eq (d :IntegralMixedPrefixSnapshot.Data) (hm :d.birth≤d.horizon)
    (cmd :IntegralMixedFullHistoryScript.Command d.source d.width) (values :ℕ→ℝ) (a b :ℝ) (he :a=b) :
    d.CutReceipt hm cmd values a↔d.CutReceipt hm cmd values b:=
  Iff.of_eq (congrArg (d.CutReceipt hm cmd values) he)

private theorem endpoint_ownReceipt_at (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid SAMP (CTX root) w)
    (j :ℕ) (hj :j<IntegralMixedCausalRecordPlanBits.count root) (b :ℕ) (hb :b=number n root+8+j) :
    IntegralMixedMarkedCutStage.ownReceipt hn ht ha hR0 root w hw j hj↔
    IntegralMixedPrefixSnapshot.familyCutReceipt P PLAN H (IntegralMixedMarkedCutStage.saved hn ht ha hR0 root b)
      ((IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j hj.le).point
        (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw))
      (IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX root) w hw b):=by
  subst b
  rfl

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

noncomputable local instance :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs
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

noncomputable def EndpointGuarded :Prop:=GuardedProgram x
  (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha c)
  (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c) z
  (IntegralMixedRoadmapProperParent.hom hn ht ha hR0 old hv hd) V
  R.result.commands R.result.room R.result.codes R.result.tuple R.result.hom R.result.nextValues

noncomputable def endpointBeforeState (i :ℕ):=
  IntegralMixedFullHistoryScript.continueRun x (R.result.commands.drop (i+1))
    (cutAt_room R.result.commands R.result.room i)

noncomputable def endpointBeforeValues (i :ℕ) (hi :i<R.result.commands.length) :ℕ→ℝ:=
  IntegralMixedFramedBankObservation.extend
    (IntegralMixedFullBankPoint.point (endpointBeforeState hn ht ha hR0 old hv hd left right R i)
      (cutAtTuple R.result.commands i hi R.result.tuple∘oldColumn R.result.commands[i]))

noncomputable def endpointNewValue (i :ℕ) (hi :i<R.result.commands.length) :ℝ:=
  IntegralMixedFullBankPoint.point
    (IntegralMixedFullHistoryScript.step (endpointBeforeState hn ht ha hR0 old hv hd left right R i)
      (cutAt_fit R.result.commands R.result.room i hi) R.result.commands[i])
    (cutAtTuple R.result.commands i hi R.result.tuple) 0

theorem endpoint_raw_lt (i :ℕ) (hi :i<R.result.commands.length) :
    (raw i)<IntegralMixedCausalRecordPlanBits.count r:=by
  have HB:=endpoint_birth_eq hn ht ha hR0 old hv hd left right R side i hi
  have HF:=endpoint_birth_lt_full hn ht ha hR0 old hv hd left right R side i hi
  unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount at HF
  omega

private theorem endpoint_initial_canonical :Canonical x:=by
  unfold IntegralMixedRoadmapRetainedAppend.parentState
  apply IntegralMixedFramedHistoryScript.reframe_canonical
  apply IntegralMixedFramedHistoryScript.run_canonical
  intro i
  exact Fin.elim0 i

private theorem endpoint_constructed_receipt (GG :EndpointGuarded hn ht ha hR0 old hv hd left right R)
    (i :ℕ) (hi :i<R.result.commands.length) :
    (IntegralMixedPrefixSnapshot.ofState (endpointBeforeState hn ht ha hR0 old hv hd left right R i)).CutReceipt
      (cutAt_fit R.result.commands R.result.room i hi) R.result.commands[i]
      (endpointBeforeValues hn ht ha hR0 old hv hd left right R i hi)
      (endpointNewValue hn ht ha hR0 old hv hd left right R i hi):=
  GuardedProgram.cut_receipt_at GG (endpoint_initial_canonical hn ht ha hR0 old hv hd)
    (IntegralMixedRoadmapProperParent.hom_generators hn ht ha hR0 old hv hd) i hi

theorem endpoint_cut_ownReceipt (GG :EndpointGuarded hn ht ha hR0 old hv hd left right R)
    (w :List Bool) (hw :SquareSampleCompleteVertices.Valid SAMP (CTX r) w)
    (i :ℕ) (hi :i<R.result.commands.length)
    (hValues :∀k<birth i,
      (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 r (raw i)
        (endpoint_raw_lt hn ht ha hR0 old hv hd left right R side i hi).le).point
        (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r w hw) k=
      endpointBeforeValues hn ht ha hR0 old hv hd left right R i hi k)
    (hHead :IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX r) w hw (birth i)=
      endpointNewValue hn ht ha hR0 old hv hd left right R i hi) :
    IntegralMixedMarkedCutStage.ownReceipt hn ht ha hR0 r w hw (raw i)
      (endpoint_raw_lt hn ht ha hR0 old hv hd left right R side i hi):=by
  let b:=birth i
  let j:=raw i
  let key:=IntegralMixedMarkedCutStage.saved hn ht ha hR0 r b
  have HFit:=endpoint_birth_lt_full hn ht ha hR0 old hv hd left right R side i hi
  have HB:=endpoint_birth_eq hn ht ha hR0 old hv hd left right R side i hi
  have HJ:=endpoint_raw_lt hn ht ha hR0 old hv hd left right R side i hi
  have HS0:=congrArg (fun a=>IntegralMixedPrefixSnapshot.ofState
    ((FAM).state (IntegralMixedMarkedCutStage.saved hn ht ha hR0 r a))) HB
  have HData:IntegralMixedPrefixSnapshot.ofState ((FAM).state key)=
      IntegralMixedPrefixSnapshot.ofState (endpointBeforeState hn ht ha hR0 old hv hd left right R i):=
    HS0.trans ((IntegralMixedMarkedCutStage.snapshot_eq hn ht ha hR0 r j HJ).trans
      (endpoint_snapshot hn ht ha hR0 old hv hd left right R side i hi))
  have HR:pairFst key=r:=
    (congrArg pairFst (IntegralMixedMarkedCutStage.saved_eq hn ht ha hR0 r b HFit)).trans
      (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
  have HChosen:HEq (IntegralMixedFramedRootPullback.instructionAt P PLAN r b).command R.result.commands[i]:=by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    exact endpoint_command hn ht ha hR0 old hv hd left right R side i hi
  have HSaved:=IntegralMixedPrefixSnapshot.instruction_command_heq _ _
      (congrArg (P).ambient HR) (congrArg (P).width HR)
      (endpoint_saved_instruction hn ht ha hR0 r b HFit)
  have HCmd:HEq (IntegralMixedFramedHistoryFamilyBits.instruction P PLAN key).command R.result.commands[i]:=
    HSaved.trans HChosen
  have HC:=endpoint_constructed_receipt hn ht ha hR0 old hv hd left right R GG i hi
  let vr:=(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 r j HJ.le).point
    (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r w hw)
  let a:=IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX r) w hw b
  have HT:=endpoint_family_receipt_transport P PLAN H key
    (IntegralMixedPrefixSnapshot.ofState (endpointBeforeState hn ht ha hR0 old hv hd left right R i))
    (cutAt_fit R.result.commands R.result.room i hi) R.result.commands[i]
    HData HCmd vr (endpointBeforeValues hn ht ha hR0 old hv hd left right R i hi) a
    (fun k hk=>hValues k (hk.trans_eq (IntegralMixedMarkedCutStage.saved_birth hn ht ha hR0 r b HFit)))
  have HCan:(IntegralMixedPrefixSnapshot.ofState (endpointBeforeState hn ht ha hR0 old hv hd left right R i)).CutReceipt
      (cutAt_fit R.result.commands R.result.room i hi) R.result.commands[i]
      (endpointBeforeValues hn ht ha hR0 old hv hd left right R i hi) a:=by
    exact (endpoint_receipt_head_eq _ _ _ _ a _ hHead).mpr HC
  have HActual:IntegralMixedPrefixSnapshot.familyCutReceipt P PLAN H key vr a:=HT.mpr HCan
  exact (endpoint_ownReceipt_at hn ht ha hR0 r w hw j HJ b HB).mpr HActual

theorem endpoint_cut_guard (GG :EndpointGuarded hn ht ha hR0 old hv hd left right R)
    (w :List Bool) (hw :SquareSampleCompleteVertices.Valid SAMP (CTX r) w)
    (i :ℕ) (hi :i<R.result.commands.length)
    (hValues :∀k<birth i,
      (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 r (raw i)
        (endpoint_raw_lt hn ht ha hR0 old hv hd left right R side i hi).le).point
        (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r w hw) k=
      endpointBeforeValues hn ht ha hR0 old hv hd left right R i hi k)
    (hHead :IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX r) w hw (birth i)=
      endpointNewValue hn ht ha hR0 old hv hd left right R i hi)
    (hc :IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha (radius_binary hR0) false
      (IntegralFramedTraceCutScan.stagePacket (pair r w) (birth i))) :
    IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha (radius_binary hR0) false
      (IntegralFramedTraceCutScan.stagePacket (pair r w) (birth i)):=by
  have HOwn:=endpoint_cut_ownReceipt hn ht ha hR0 old hv hd left right R side GG w hw i hi hValues hHead
  have HB:=endpoint_birth_eq hn ht ha hR0 old hv hd left right R side i hi
  have HP:=((endpoint_stageCut_iff hn ht ha hR0 r w (birth i)).mp hc)
  have HP':IntegralFramedCreatingCut.ParentCut P PLAN
      (IntegralMixedMarkedCutStage.parent hn ht ha hR0 r (number n r+8+raw i)):=by
    simpa only [HB] using HP
  have HG:=IntegralMixedMarkedCutStage.guard_of_ownReceipt hn ht ha hR0 r w hw (raw i)
    (endpoint_raw_lt hn ht ha hR0 old hv hd left right R side i hi) HP' HOwn
  simpa only [IntegralFramedTraceCutScan.stagePacket,IntegralMixedPhysicalCutCoefficientSemantics.stage,
    pairFst_pair,pairSnd_pair,HB] using HG

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
