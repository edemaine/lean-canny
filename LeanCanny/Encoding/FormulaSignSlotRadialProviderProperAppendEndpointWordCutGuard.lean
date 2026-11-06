/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendEndpointSnapshot
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutSemantics
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendSampledLevel
public import LeanCanny.Geometry.IntegralMixedGuardedProgramCutValues
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendScalarReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixFields
/-! # Constructed endpoint receipts give actual own-word native cut guards

The two numerical readbacks are explicit intermediate contracts. Creating
snapshots, commands, parent canonicality and generator identities are derived.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedOptionalEndpoints
open IntegralMixedChronologicalEndpoint IntegralMixedChosenLocalRealization UniformIntegralPowerSchedule
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "PLAN"=>FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H"=>FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "FAM"=>IntegralMixedFramedHistoryFamilyBits.family P PLAN H
local notation "SAMP"=>FormulaSignSlotRadialProviderAtomic.input
local notation "CTX" root=>FormulaSignSlotRadialProviderRecordPrefix.context root

private theorem endpoint_saved_instruction (root :List Bool) (b :ℕ)
    (hb :b<FormulaSignSlotRadialProviderRecordPlan.fullCount root) :
    HEq (IntegralMixedFramedHistoryFamilyBits.instruction P PLAN
      (FormulaSignSlotRadialProviderRecordPrefix.cutSaved root b))
      (IntegralMixedFramedRootPullback.instructionAt P PLAN root b):=by
  let key:=FormulaSignSlotRadialProviderRecordPrefix.cutSaved root b
  have HR :pairFst key=root:=
    (congrArg pairFst (FormulaSignSlotRadialProviderRecordPrefix.cutSaved_eq root b hb)).trans
      (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
  have HP :IntegralMixedFramedHistoryFamilyBits.prefixLength P key=b:=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P PLAN H key).symm.trans
      (FormulaSignSlotRadialProviderRecordPrefix.cutSaved_birth root b hb)
  exact IntegralMixedFramedRootPullback.instructionAt_congr P PLAN _ root _ b HR HP

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
    (j :ℕ) (hj :j<IntegralMixedCausalRecordPlanBits.count root) (b :ℕ) (hb :b=FormulaSignSlotRadialProviderRecordPlan.count root+j) :
    FormulaSignSlotRadialProviderRecordPrefix.ownCutReceipt root w hw j hj↔
    IntegralMixedPrefixSnapshot.familyCutReceipt P PLAN H (FormulaSignSlotRadialProviderRecordPrefix.cutSaved root b)
      ((FormulaSignSlotRadialProviderRecordPrefix.observation root j hj.le).point
        (FormulaSignSlotRadialProviderRecordPrefix.natural root w hw))
      (FormulaSignSlotRadialProviderAtomic.bankField (CTX root) w hw b):=by
  subst b
  rfl

variable (old :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd :FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "e"=>FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he"=>FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c"=>FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "oldCs"=>FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "x"=>FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd e he
local notation "parentZ"=>FormulaSignSlotRadialProviderRetainedAppend.parentTuple old hv hd e he
local notation "V"=>FormulaSignSlotRadialProviderRetainedAppend.parentValues old hv hd e he
variable (left right :ParentEndpoint old hv hd)
  (R :CanonicalPair old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot old R.leftSpec R.rightSpec side
local notation "birth" i=>endpointBirth old hv hd left right R i
local notation "raw" i=>endpointRawIndex old hv hd left right R i

noncomputable local instance providerProperEndpointCutFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderRecordPrefix.ownCutReceipt
  FormulaSignSlotRadialProviderAtomic.Cuts.Guards FormulaSignSlotRadialProviderAtomic.Cuts.StageCut
  IntegralMixedPrefixSnapshot.familyCutReceipt
  FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  IntegralMixedFramedHistoryFamilyBits.family IntegralFramedPhysicalBankTerm.env
  FormulaSignSlotRadialProviderRecordPrefix.observation FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderAtomic.dimension
  FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.depth

noncomputable def EndpointGuarded :Prop:=GuardedProgram x
  (FormulaSignSlotRadialProviderRecordPlan.positive c)
  (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap c) parentZ
  (FormulaSignSlotRadialProviderRetainedAppend.parentHom old hv hd e he) V
  R.result.commands R.result.room R.result.codes R.result.tuple R.result.hom R.result.nextValues

noncomputable def endpointBeforeState (i :ℕ):=
  IntegralMixedFullHistoryScript.continueRun x (R.result.commands.drop (i+1))
    (cutAt_room R.result.commands R.result.room i)

noncomputable def endpointBeforeValues (i :ℕ) (hi :i<R.result.commands.length) :ℕ→ℝ:=
  IntegralMixedFramedBankObservation.extend
    (IntegralMixedFullBankPoint.point (endpointBeforeState old hv hd left right R i)
      (cutAtTuple R.result.commands i hi R.result.tuple∘oldColumn R.result.commands[i]))

noncomputable def endpointNewValue (i :ℕ) (hi :i<R.result.commands.length) :ℝ:=
  IntegralMixedFullBankPoint.point
    (IntegralMixedFullHistoryScript.step (endpointBeforeState old hv hd left right R i)
      (cutAt_fit R.result.commands R.result.room i hi) R.result.commands[i])
    (cutAtTuple R.result.commands i hi R.result.tuple) 0

theorem endpoint_raw_lt (i :ℕ) (hi :i<R.result.commands.length) :
    (raw i)<IntegralMixedCausalRecordPlanBits.count r:=by
  have HB:=endpoint_birth_eq old hv hd left right R side i hi
  have HF:=endpoint_birth_lt_full old hv hd left right R side i hi
  unfold FormulaSignSlotRadialProviderRecordPlan.fullCount at HF
  omega

private theorem endpoint_initial_canonical :Canonical x:=by
  unfold FormulaSignSlotRadialProviderRetainedAppend.parentState
  apply IntegralMixedFramedHistoryScript.reframe_canonical
  apply IntegralMixedFramedHistoryScript.run_canonical
  intro i
  exact Fin.elim0 i

private theorem endpoint_constructed_receipt (GG :EndpointGuarded old hv hd left right R)
    (i :ℕ) (hi :i<R.result.commands.length) :
    (IntegralMixedPrefixSnapshot.ofState (endpointBeforeState old hv hd left right R i)).CutReceipt
      (cutAt_fit R.result.commands R.result.room i hi) R.result.commands[i]
      (endpointBeforeValues old hv hd left right R i hi)
      (endpointNewValue old hv hd left right R i hi):=
  GuardedProgram.cut_receipt_at GG (endpoint_initial_canonical old hv hd)
    (FormulaSignSlotRadialProviderRetainedAppend.parentHom_generators old hv hd e he) i hi

theorem endpoint_cut_ownReceipt (GG :EndpointGuarded old hv hd left right R)
    (w :List Bool) (hw :SquareSampleCompleteVertices.Valid SAMP (CTX r) w)
    (i :ℕ) (hi :i<R.result.commands.length)
    (hValues :∀k<birth i,
      (FormulaSignSlotRadialProviderRecordPrefix.observation r (raw i)
        (endpoint_raw_lt old hv hd left right R side i hi).le).point
        (FormulaSignSlotRadialProviderRecordPrefix.natural r w hw) k=
      endpointBeforeValues old hv hd left right R i hi k)
    (hHead :FormulaSignSlotRadialProviderAtomic.bankField (CTX r) w hw (birth i)=
      endpointNewValue old hv hd left right R i hi) :
    FormulaSignSlotRadialProviderRecordPrefix.ownCutReceipt r w hw (raw i)
      (endpoint_raw_lt old hv hd left right R side i hi):=by
  let b:=birth i
  let j:=raw i
  let key:=FormulaSignSlotRadialProviderRecordPrefix.cutSaved r b
  have HFit:=endpoint_birth_lt_full old hv hd left right R side i hi
  have HB:=endpoint_birth_eq old hv hd left right R side i hi
  have HJ:=endpoint_raw_lt old hv hd left right R side i hi
  have HS0:=congrArg (fun a=>IntegralMixedPrefixSnapshot.ofState
    ((FAM).state (FormulaSignSlotRadialProviderRecordPrefix.cutSaved r a))) HB
  have HData:IntegralMixedPrefixSnapshot.ofState ((FAM).state key)=
      IntegralMixedPrefixSnapshot.ofState (endpointBeforeState old hv hd left right R i):=
    HS0.trans ((FormulaSignSlotRadialProviderRecordPrefix.cut_snapshot r j HJ).trans
      (endpoint_snapshot old hv hd left right R side i hi))
  have HR:pairFst key=r:=
    (congrArg pairFst (FormulaSignSlotRadialProviderRecordPrefix.cutSaved_eq r b HFit)).trans
      (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
  have HChosen:HEq (IntegralMixedFramedRootPullback.instructionAt P PLAN r b).command R.result.commands[i]:=by
    exact endpoint_command old hv hd left right R side i hi
  have HSaved:=IntegralMixedPrefixSnapshot.instruction_command_heq _ _
      (congrArg (P).ambient HR) (congrArg (P).width HR)
      (endpoint_saved_instruction r b HFit)
  have HCmd:HEq (IntegralMixedFramedHistoryFamilyBits.instruction P PLAN key).command R.result.commands[i]:=
    HSaved.trans HChosen
  have HC:=endpoint_constructed_receipt old hv hd left right R GG i hi
  let vr:=(FormulaSignSlotRadialProviderRecordPrefix.observation r j HJ.le).point
    (FormulaSignSlotRadialProviderRecordPrefix.natural r w hw)
  let a:=FormulaSignSlotRadialProviderAtomic.bankField (CTX r) w hw b
  have HT:=endpoint_family_receipt_transport P PLAN H key
    (IntegralMixedPrefixSnapshot.ofState (endpointBeforeState old hv hd left right R i))
    (cutAt_fit R.result.commands R.result.room i hi) R.result.commands[i]
    HData HCmd vr (endpointBeforeValues old hv hd left right R i hi) a
    (fun k hk=>hValues k (hk.trans_eq (FormulaSignSlotRadialProviderRecordPrefix.cutSaved_birth r b HFit)))
  have HCan:(IntegralMixedPrefixSnapshot.ofState (endpointBeforeState old hv hd left right R i)).CutReceipt
      (cutAt_fit R.result.commands R.result.room i hi) R.result.commands[i]
      (endpointBeforeValues old hv hd left right R i hi) a:=by
    exact (endpoint_receipt_head_eq _ _ _ _ a _ hHead).mpr HC
  have HActual:IntegralMixedPrefixSnapshot.familyCutReceipt P PLAN H key vr a:=HT.mpr HCan
  exact (endpoint_ownReceipt_at r w hw j HJ b HB).mpr HActual

theorem endpoint_cut_guard (GG :EndpointGuarded old hv hd left right R)
    (w :List Bool) (hw :SquareSampleCompleteVertices.Valid SAMP (CTX r) w)
    (i :ℕ) (hi :i<R.result.commands.length)
    (hValues :∀k<birth i,
      (FormulaSignSlotRadialProviderRecordPrefix.observation r (raw i)
        (endpoint_raw_lt old hv hd left right R side i hi).le).point
        (FormulaSignSlotRadialProviderRecordPrefix.natural r w hw) k=
      endpointBeforeValues old hv hd left right R i hi k)
    (hHead :FormulaSignSlotRadialProviderAtomic.bankField (CTX r) w hw (birth i)=
      endpointNewValue old hv hd left right R i hi)
    (hc :FormulaSignSlotRadialProviderAtomic.Cuts.StageCut
      (IntegralFramedTraceCutScan.stagePacket (pair r w) (birth i))) :
    FormulaSignSlotRadialProviderAtomic.Cuts.Guards
      (IntegralFramedTraceCutScan.stagePacket (pair r w) (birth i)):=by
  have HOwn:=endpoint_cut_ownReceipt old hv hd left right R side GG w hw i hi hValues hHead
  have HB:=endpoint_birth_eq old hv hd left right R side i hi
  have HJ:=endpoint_raw_lt old hv hd left right R side i hi
  have HNew :FormulaSignSlotRadialProviderAtomic.Cuts.StageCut
      (FormulaSignSlotRadialProviderCutReadback.stage r w
        (FormulaSignSlotRadialProviderRecordPlan.count r+raw i)):=by
    simpa only [FormulaSignSlotRadialProviderCutReadback.stage,HB] using hc
  have HG:=(FormulaSignSlotRadialProviderCutSemantics.guards_iff_ownReceipt r w hw (raw i) HJ HNew).mpr HOwn
  simpa only [FormulaSignSlotRadialProviderCutReadback.stage,HB] using HG

local notation "hk"=>FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "g"=>FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he
local notation "js"=>R.orderedFree hk
local notation "K"=>List.length js
local notation "M"=>List.length oldCs+List.length R.result.commands
local notation "C"=>canonicalObservation old hv hd left right R side
local notation "finish"=>finishBirth old hv hd left right R side
open IntegralMixedChronologicalLevelScalarValues

theorem endpoint_program_values (GG :EndpointGuarded old hv hd left right R)
    (i :ℕ) (hi :i<R.result.commands.length) :
    CutAtValues x R.result.commands R.result.room R.result.tuple R.result.nextValues i hi:=
  GuardedProgram.cut_at_values GG (endpoint_initial_canonical old hv hd)
    (FormulaSignSlotRadialProviderRetainedAppend.parentHom_generators old hv hd e he)
    (FormulaSignSlotRadialProviderRetainedAppend.parentHom_quotients old hv hd e he) i hi

theorem WordReceipt.endpoint_field_at {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀j :Fin (M+1+K+1+K),(C).point z j.val=levelValues pMID pChild R.result.nextValues g js j)
    (k :Fin M) :
    FormulaSignSlotRadialProviderAtomic.bankField (CTX r) W.word W.valid
      (beginBirth old+R.result.commands.length-1-k.val)=R.result.nextValues k:=by
  have HP:=FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd e he
  change (oldCs).length=beginBirth old at HP
  have HF:finish=beginBirth old+R.result.commands.length+2+2*K:=by
    unfold finishBirth
    rw [R.levelCodes_length]
    omega
  have HB:beginBirth old+R.result.commands.length-1-k.val<finish:=by omega
  have HClock:finish-1-(beginBirth old+R.result.commands.length-1-k.val)=K+1+(K+1+k.val):=by
    have HK:=k.isLt
    omega
  have HW:=W.local_field _ HB
  rw [HClock] at HW
  exact HW.trans ((hValues ⟨K+1+(K+1+k.val),by have HK:=k.isLt;omega⟩).trans
    (IntegralMixedChronologicalLevelScalarValues.endpoint_value pMID pChild R.result.nextValues g js k))

theorem WordReceipt.endpoint_new_value {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀j :Fin (M+1+K+1+K),(C).point z j.val=levelValues pMID pChild R.result.nextValues g js j)
    (GG :EndpointGuarded old hv hd left right R) (i :ℕ) (hi :i<R.result.commands.length) :
    FormulaSignSlotRadialProviderAtomic.bankField (CTX r) W.word W.valid (birth i)=
      endpointNewValue old hv hd left right R i hi:=by
  have HG:=(endpoint_program_values old hv hd left right R GG i hi).1
  have HW:=W.endpoint_field_at old hv hd left right R side pMID pChild hValues
    (cutAtHeadIndex (oldCs).length R.result.commands i hi)
  exact HW.trans HG.symm

private theorem endpoint_before_birth (i :ℕ) (hi :i<R.result.commands.length) :
    (oldCs).length+(R.result.commands.drop (i+1)).length=birth i:=by
  have HB:=cutAt_birth (m:=(oldCs).length) R.result.commands i hi
  have HP:=FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd e he
  change (oldCs).length=beginBirth old at HP
  unfold endpointBirth
  omega

private theorem endpoint_extend_finite {k :ℕ} (f :Fin k→ℝ) (i :Fin k) :
    IntegralMixedFramedBankObservation.extend f i.val=f i:=by
  simp only [IntegralMixedFramedBankObservation.extend,dite_eq_left i.isLt]

theorem WordReceipt.endpoint_before_values {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀j :Fin (M+1+K+1+K),(C).point z j.val=levelValues pMID pChild R.result.nextValues g js j)
    (GG :EndpointGuarded old hv hd left right R) (i :ℕ) (hi :i<R.result.commands.length)
    (k :ℕ) (hkb :k<birth i) :
    (FormulaSignSlotRadialProviderRecordPrefix.observation r (raw i)
      (endpoint_raw_lt old hv hd left right R side i hi).le).point
      (FormulaSignSlotRadialProviderRecordPrefix.natural r W.word W.valid) k=
      endpointBeforeValues old hv hd left right R i hi k:=by
  have HB:=endpoint_before_birth old hv hd left right R i hi
  let j :Fin ((oldCs).length+(R.result.commands.drop (i+1)).length):=⟨k,by omega⟩
  let idx:=cutAtBeforeIndex (oldCs).length R.result.commands i hi j
  have HG:=(endpoint_program_values old hv hd left right R GG i hi).2 j
  have HCan:endpointBeforeValues old hv hd left right R i hi k=R.result.nextValues idx:=by
    change IntegralMixedFramedBankObservation.extend
      (IntegralMixedFullBankPoint.point (endpointBeforeState old hv hd left right R i)
        (cutAtTuple R.result.commands i hi R.result.tuple∘oldColumn R.result.commands[i])) k=_
    exact (endpoint_extend_finite _ j).trans HG
  have HW:=W.endpoint_field_at old hv hd left right R side pMID pChild hValues idx
  have HE:=endpoint_birth_eq old hv hd left right R side i hi
  have HP:=FormulaSignSlotRadialProviderRecordPrefix.word_value r W.word W.valid (raw i)
    (endpoint_raw_lt old hv hd left right R side i hi).le k (hkb.trans_eq HE)
  have HClock:FormulaSignSlotRadialProviderRecordPlan.count r+(raw i)-1-k=
      beginBirth old+R.result.commands.length-1-idx.val:=by
    dsimp only [idx,cutAtBeforeIndex,j]
    unfold endpointBirth at HE
    omega
  exact HP.trans ((congrArg (FormulaSignSlotRadialProviderAtomic.bankField (CTX r) W.word W.valid)
    HClock).trans HW) |>.trans HCan.symm

theorem WordReceipt.endpoint_native_cut_guard {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀j :Fin (M+1+K+1+K),(C).point z j.val=levelValues pMID pChild R.result.nextValues g js j)
    (GG :EndpointGuarded old hv hd left right R) (i :ℕ) (hi :i<R.result.commands.length)
    (hc :FormulaSignSlotRadialProviderAtomic.Cuts.StageCut
      (IntegralFramedTraceCutScan.stagePacket (pair r W.word) (birth i))) :
    FormulaSignSlotRadialProviderAtomic.Cuts.Guards
      (IntegralFramedTraceCutScan.stagePacket (pair r W.word) (birth i)):=
  endpoint_cut_guard old hv hd left right R side GG W.word W.valid i hi
    (W.endpoint_before_values old hv hd left right R side pMID pChild hValues GG i hi)
    (W.endpoint_new_value old hv hd left right R side pMID pChild hValues GG i hi) hc

theorem SampledLevel.endpoint_cut_guard
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (S :SampledLevel old hv hd left right R side pMID pChild)
    (b :ℕ) (hb0 :beginBirth old≤b) (hb1 :b<midpointBirth old hv hd left right R)
    (hc :FormulaSignSlotRadialProviderAtomic.Cuts.StageCut
      (IntegralFramedTraceCutScan.stagePacket (pair r S.receipt.word) b)) :
    FormulaSignSlotRadialProviderAtomic.Cuts.Guards
      (IntegralFramedTraceCutScan.stagePacket (pair r S.receipt.word) b):=by
  let i:=beginBirth old+R.result.commands.length-1-b
  have HI:i<R.result.commands.length:=by unfold midpointBirth at hb1;dsimp only [i];omega
  have HB:(birth i)=b:=by unfold endpointBirth;dsimp only [i];unfold midpointBirth at hb1;omega
  obtain ⟨A,E,ordinal,HE,N⟩:=S.physical
  have HV:∀j :Fin (M+1+K+1+K),(C).point S.localTuple j.val=
      levelValues pMID pChild R.result.nextValues g js j:=N.bank_values
  have HG:=S.receipt.endpoint_native_cut_guard old hv hd left right R side pMID pChild HV
    N.endpoint_trace i HI (by simpa only [HB] using hc)
  simpa only [HB] using HG

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
