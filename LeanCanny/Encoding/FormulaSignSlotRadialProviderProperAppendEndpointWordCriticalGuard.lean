/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendEndpointWordCutGuard
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicPointLanguage
public import LeanCanny.Geometry.IntegralMixedChronologicalEndpointPhysicalColumns
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalLayout
/-! # The same endpoint tuple supplies its native critical correlations -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalEndpoint
open IntegralMixedOptionalEndpoints IntegralMixedChosenLocalRealization
open IntegralMixedFramedPhysicalIndex (arity prefixArity enumerate)
open IntegralMixedFramedHistoryFamilyBits (defaultInstruction)
open IntegralMixedFramedFixedContinuation (wrap)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem critical_header_context {n B :ℕ} {Q :SpatialSource n}
    (cmd :IntegralMixedFullHistoryScript.Command Q B)
    (hc :(IntegralMixedCommandHeaderBits.command cmd).context=1) :cmd.isCritical=true:=by
  cases cmd with
  | integer=>cases hc
  | critical=>rfl
  | cut r k d hs hd=>cases k <;> cases hc

private theorem critical_arity_heq {n m B C :ℕ} (cs :List (Instruction n B)) (ds :List (Instruction m C))
    (hn :n=m) (hB :B=C) (he :HEq cs ds) :arity cs=arity ds:=by
  subst m;subst C
  cases eq_of_heq he
  rfl

private theorem block_bankNatural (B :IntegralFramedBankQuery.Bank) (T :IntegralMixedHeaderTablesBits.Tables)
    (c w :List Bool) (hw :SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (b i :ℕ)
    (hc :prefixArity B.parameters T (pair (B.key c) (List.replicate b true))+i<
      (IntegralFramedPhysicalBankTerm.input B).count c) :
    IntegralFramedPhysicalCompanionPoint.block B T c w hw b i=
      FormulaSignSlotRadialProviderRecordPrefix.bankNatural B c w hw
        (prefixArity B.parameters T (pair (B.key c) (List.replicate b true))+i)^
        IntegralMixedFramedCriticalGuardBits.physicalPower B.parameters B.key (fun _=>b) c:=by
  unfold IntegralFramedPhysicalCompanionPoint.block
  rw [dite_eq_left hc]
  unfold FormulaSignSlotRadialProviderRecordPrefix.bankNatural IntegralFramedPhysicalPrefixObservation.tuple
    IntegralMixedFramedBankObservation.extend
  split_ifs with hc2
  · rfl
  · exact False.elim (hc2 hc)

local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D"=>FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "T"=>FormulaSignSlotRadialProviderRecordPlan.tables
local notation "CTX" root=>FormulaSignSlotRadialProviderRecordPrefix.context root
variable (old :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd :FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "e"=>FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he"=>FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c"=>FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "oldCs"=>FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "x"=>FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd e he
local notation "hk"=>FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "g"=>FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he
local notation "hg"=>FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd e he
variable (left right :ParentEndpoint old hv hd) (R :CanonicalPair old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot old R.leftSpec R.rightSpec side
local notation "birth" i=>endpointBirth old hv hd left right R i
local notation "js"=>R.orderedFree hk
local notation "K"=>List.length js
local notation "C"=>canonicalObservation old hv hd left right R side
noncomputable local instance providerProperEndpointCriticalFintype :Fintype (Index (Fin 0) oldCs):=
  indexFintype (Fin 0) oldCs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  IntegralMixedFramedHistoryFamilyBits.family
  preparedRoot FormulaSignSlotRadialProviderRetainedAppend.preparedRoot
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth

private theorem endpoint_critical_provider :FormulaSignSlotRadialProviderRecordPlan.providerContext r=
    FormulaSignSlotRadialProviderRecordPlan.providerContext c:=
  (prepared_provider old R.leftSpec R.rightSpec side).trans
    (FormulaSignSlotRadialProviderRetainedAppend.prepared_provider old e).symm

private theorem endpoint_critical_resources :(P).cap r=(P).cap c ∧(P).width r=(P).width c:=by
  have HC:IntegralMixedCausalRecordPlanBits.count r=IntegralMixedCausalRecordPlanBits.count c:=
    (prepared_count old hv hd R.leftSpec R.rightSpec side (endpoints_good old hv hd left right R)).trans
      (FormulaSignSlotRadialProviderRetainedAppend.prepared_count old hv hd e he).symm
  exact ⟨FormulaSignSlotRadialProviderRecordPrefix.cap r c
    (endpoint_critical_provider old hv hd left right R side) HC,
    FormulaSignSlotRadialProviderRecordPrefix.width r c (endpoint_critical_provider old hv hd left right R side)⟩

theorem endpoint_native_header (i :ℕ) (hi :i<R.result.commands.length) :
    FormulaSignSlotRadialProviderRecordPrefix.header r (birth i)=
      IntegralMixedCommandHeaderBits.command R.result.commands[i]:=by
  have HI:=endpoint_instruction old hv hd left right R side i hi
  have HH:=IntegralMixedFramedRootPullback.instruction_read
    (fun _ _ I=>IntegralMixedCommandHeaderBits.command I.command) _ _
    (FormulaSignSlotRadialProviderRecordPrefix.ambient r c (endpoint_critical_provider old hv hd left right R side))
    (FormulaSignSlotRadialProviderRecordPrefix.width r c (endpoint_critical_provider old hv hd left right R side)) HI
  exact (FormulaSignSlotRadialProviderRecordPrefix.header_actual r (birth i)).trans HH

theorem endpoint_critical_tag (i :ℕ) (hi :i<R.result.commands.length)
    (hb :FormulaSignSlotRadialProviderAtomic.Active (CTX r) (birth i)) :R.result.commands[i].isCritical=true:=by
  have HH:(FormulaSignSlotRadialProviderRecordPrefix.header r (birth i)).context=1:=hb.2
  rw [endpoint_native_header old hv hd left right R side i hi] at HH
  exact critical_header_context _ HH

theorem endpoint_selected_critical (i :ℕ) (hi :i<R.result.commands.length)
    (rule :CriticalRule ((P).ambient c)) (hc :R.result.commands[i]=.critical rule) :
    FormulaSignSlotRadialProviderAtomic.selected (CTX r) (birth i)=
      rule.offset.val+rule.coordinate%((P).ambient c-rule.offset.val+1):=by
  change (FormulaSignSlotRadialProviderRecordPrefix.header r (birth i)).offset+
    (FormulaSignSlotRadialProviderRecordPrefix.header r (birth i)).coordinate=_
  rw [endpoint_native_header old hv hd left right R side i hi,hc]
  rfl

theorem endpoint_prefix_arity (i :ℕ) (hi :i<R.result.commands.length) :
    prefixArity P T (pair ((BK).key (CTX r)) (List.replicate (birth i) true))=
      arity (endpointPartialCommands old hv hd left right R i):=by
  rw [IntegralMixedFramedPhysicalIndex.prefixArity_packet P D (BK).data T FormulaSignSlotRadialProviderAtomic.bank_represents,
    FormulaSignSlotRadialProviderRecordPrefix.key_root]
  exact critical_arity_heq _ _
    (FormulaSignSlotRadialProviderRecordPrefix.ambient r c (endpoint_critical_provider old hv hd left right R side))
    (FormulaSignSlotRadialProviderRecordPrefix.width r c (endpoint_critical_provider old hv hd left right R side))
    (endpoint_prefix_commands old hv hd left right R side i hi)

noncomputable def endpointPhysicalValue (i :ℕ) (hi :i<R.result.commands.length) :ℝ:=
  selectedPhysical (endpointBeforeState old hv hd left right R i)
    (cutAt_fit R.result.commands R.result.room i hi) R.result.commands[i]
    (cutAtTuple R.result.commands i hi R.result.tuple)

private theorem endpoint_critical_initial_canonical :Canonical x:=by
  unfold FormulaSignSlotRadialProviderRetainedAppend.parentState
  apply IntegralMixedFramedHistoryScript.reframe_canonical
  apply IntegralMixedFramedHistoryScript.run_canonical
  intro i
  exact Fin.elim0 i

theorem endpoint_constructed_correlation (GG :EndpointGuarded old hv hd left right R)
    (i :ℕ) (hi :i<R.result.commands.length) (hc :R.result.commands[i].isCritical=true) :
    endpointNewValue old hv hd left right R i hi=endpointPhysicalValue old hv hd left right R i hi:=
  GuardedProgram.critical_at GG (endpoint_critical_initial_canonical old hv hd)
    (FormulaSignSlotRadialProviderRetainedAppend.parentHom_generators old hv hd e he) i hi hc

private theorem endpoint_critical_birth (i :ℕ) (hi :i<R.result.commands.length) :
    (birth i)=(oldCs).length+(R.result.commands.drop (i+1)).length:=by
  have HB:=cutAt_birth (m:=(oldCs).length) R.result.commands i hi
  have HP:=FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd e he
  change (oldCs).length=beginBirth old at HP
  unfold endpointBirth
  omega

private theorem endpoint_partial_arity (i :ℕ) :
    arity (endpointPartialCommands old hv hd left right R i)=
      arity (List.append (α:=Instruction ((P).ambient c) ((P).width c))
        ((R.result.commands.drop (i+1)).map
          (wrap (FormulaSignSlotRadialProviderRecordPlan.spatial c)
            (IntegralMixedStaticRecordPrefix.cap _
              (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap c)))) oldCs):=by
  unfold endpointPartialCommands canonicalEndpointWrap
  rfl

private theorem command_critical_exists {n B :ℕ} {Q :SpatialSource n}
    (cmd :IntegralMixedFullHistoryScript.Command Q B) (hc :cmd.isCritical=true) :
    ∃rule,cmd=.critical rule:=by
  cases cmd with
  | integer=>cases hc
  | critical rule=>exact ⟨rule,rfl⟩
  | cut=>cases hc

private theorem endpoint_critical_bank_parameters :(BK).parameters=P:=rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  canonicalObservation

theorem WordReceipt.endpoint_selected_physical {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt old hv hd left right R side u p0)
    (layout :R.levelIndex hk g hg side≃Fin (C).arity)
    (hLayout :HEq (enumerate (canonicalCompiledProgram old hv hd left right R side)) layout)
    (hPair :∀p :IntegralMixedFullHistoryScript.Index (Index (Fin 0) oldCs) R.result.commands,
      u (layout (R.levelPairColumn hk g hg side p)).val=R.result.tuple p)
    (i :ℕ) (hi :i<R.result.commands.length)
    (hb :FormulaSignSlotRadialProviderAtomic.Active (CTX r) (birth i)) :
    FormulaSignSlotRadialProviderAtomic.geometricPoint (CTX r) W.word W.valid (birth i)
      ⟨FormulaSignSlotRadialProviderAtomic.selected (CTX r) (birth i),
        FormulaSignSlotRadialProviderAtomic.selected_lt _ _ hb⟩=
      endpointPhysicalValue old hv hd left right R i hi:=by
  obtain ⟨rule,HC⟩:=command_critical_exists R.result.commands[i]
    (endpoint_critical_tag old hv hd left right R side i hi hb)
  let p:=criticalAtColumn oldCs R.result.commands i hi rule HC (criticalCoordinate rule)
  let q:=arity (endpointPartialCommands old hv hd left right R i)+(criticalCoordinate rule).val
  have HNumber:(layout (R.levelPairColumn hk g hg side p)).val=q:=by
    dsimp only [p,q]
    rw [endpoint_partial_arity old hv hd left right R i]
    exact R.level_endpoint_critical_number
      (IntegralMixedStaticRecordPrefix.cap _ (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap c))
      oldCs hk g hg side layout hLayout i hi rule HC (criticalCoordinate rule)
  have HRaw:W.tuple q=R.result.tuple p:=
    (congrArg W.tuple HNumber).symm.trans
      ((W.preserved _ (layout (R.levelPairColumn hk g hg side p)).isLt).trans (hPair p))
  have HIndex:prefixArity P T (pair ((BK).key (CTX r)) (List.replicate (birth i) true))+
      FormulaSignSlotRadialProviderAtomic.selected (CTX r) (birth i)=q:=by
    rw [endpoint_prefix_arity old hv hd left right R side i hi,
      endpoint_selected_critical old hv hd left right R side i hi rule HC]
    rfl
  have Hq:q<(C).arity:=by
    rw [←HNumber]
    exact (layout (R.levelPairColumn hk g hg side p)).isLt
  have HFull:q<arity ((D).rules r):=Hq.trans_le (canonical_arity_le_full old hv hd left right R side)
  have HCount:q<(FormulaSignSlotRadialProviderAtomic.input).count (CTX r):=
    HFull.trans_eq (sampled_arity old hv hd left right R side).symm
  have HBlock:=block_bankNatural BK T (CTX r) W.word W.valid (birth i)
    (FormulaSignSlotRadialProviderAtomic.selected (CTX r) (birth i)) (by rw [endpoint_critical_bank_parameters,HIndex];exact HCount)
  have HNat:=W.natural_eq q HFull
  have HP:=selectedPhysical_at_column oldCs x R.result.commands R.result.room R.result.tuple i hi rule HC
  change endpointPhysicalValue old hv hd left right R i hi=
    R.result.tuple p^UniformIntegralPowerSchedule.physical ((P).cap c+1) (2^(P).width c)
      ((oldCs).length+(R.result.commands.drop (i+1)).length) at HP
  change FormulaSignSlotRadialProviderAtomic.geometricPoint (CTX r) W.word W.valid (birth i)
      ⟨FormulaSignSlotRadialProviderAtomic.selected (CTX r) (birth i),
        FormulaSignSlotRadialProviderAtomic.selected_lt _ _ hb⟩=
    FormulaSignSlotRadialProviderRecordPrefix.natural r W.word W.valid
      (prefixArity (BK).parameters T (pair ((BK).key (CTX r)) (List.replicate (birth i) true))+
        FormulaSignSlotRadialProviderAtomic.selected (CTX r) (birth i))^
      UniformIntegralPowerSchedule.physical ((BK).parameters.cap (pairFst ((BK).key (CTX r)))+1)
        (2^(BK).parameters.width (pairFst ((BK).key (CTX r)))) (birth i) at HBlock
  have HIndexB:prefixArity (BK).parameters T (pair ((BK).key (CTX r)) (List.replicate (birth i) true))+
      FormulaSignSlotRadialProviderAtomic.selected (CTX r) (birth i)=q:=
    (congrArg (fun A=>prefixArity A T (pair ((BK).key (CTX r)) (List.replicate (birth i) true))+
      FormulaSignSlotRadialProviderAtomic.selected (CTX r) (birth i)) endpoint_critical_bank_parameters).trans HIndex
  have HPower:UniformIntegralPowerSchedule.physical
      ((BK).parameters.cap (pairFst ((BK).key (CTX r)))+1)
      (2^(BK).parameters.width (pairFst ((BK).key (CTX r)))) (birth i)=
      UniformIntegralPowerSchedule.physical ((P).cap c+1) (2^(P).width c)
        ((oldCs).length+(R.result.commands.drop (i+1)).length):=by
    rw [endpoint_critical_bank_parameters,FormulaSignSlotRadialProviderRecordPrefix.key_root,
      (endpoint_critical_resources old hv hd left right R side).1,
      (endpoint_critical_resources old hv hd left right R side).2,
      endpoint_critical_birth old hv hd left right R i hi]
  have HBase:FormulaSignSlotRadialProviderRecordPrefix.natural r W.word W.valid
      (prefixArity (BK).parameters T (pair ((BK).key (CTX r)) (List.replicate (birth i) true))+
        FormulaSignSlotRadialProviderAtomic.selected (CTX r) (birth i))=R.result.tuple p:=
    (congrArg (FormulaSignSlotRadialProviderRecordPrefix.natural r W.word W.valid) HIndexB).trans
      (HNat.trans HRaw)
  exact HBlock.trans ((congrArg₂ (fun (a :ℝ) (n :ℕ)=>a^n) HBase HPower).trans HP.symm)

theorem WordReceipt.endpoint_native_critical_guard {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt old hv hd left right R side u p0)
    (layout :R.levelIndex hk g hg side≃Fin (C).arity)
    (hLayout :HEq (enumerate (canonicalCompiledProgram old hv hd left right R side)) layout)
    (hPair :∀p :IntegralMixedFullHistoryScript.Index (Index (Fin 0) oldCs) R.result.commands,
      u (layout (R.levelPairColumn hk g hg side p)).val=R.result.tuple p)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀j :Fin ((oldCs).length+R.result.commands.length+1+K+1+K),
      (C).point u j.val=IntegralMixedChronologicalLevelScalarValues.levelValues
        pMID pChild R.result.nextValues g js j)
    (GG :EndpointGuarded old hv hd left right R)
    (i :ℕ) (hi :i<R.result.commands.length)
    (hb :FormulaSignSlotRadialProviderAtomic.Active (CTX r) (birth i)) :
    IntegralFramedPhysicalCompanionPoint.scalarValue BK T FormulaSignSlotRadialProviderAtomic.bank_represents
      (CTX r) W.word (birth i)=InfinitesimalSign.encode 0:=by
  apply (FormulaSignSlotRadialProviderAtomic.scalarValue_zero_iff_field (CTX r) W.word W.valid (birth i) hb).mpr
  exact (W.endpoint_new_value old hv hd left right R side pMID pChild hValues GG i hi).trans
    ((endpoint_constructed_correlation old hv hd left right R GG i hi
      (endpoint_critical_tag old hv hd left right R side i hi hb)).trans
      (W.endpoint_selected_physical old hv hd left right R side layout hLayout hPair i hi hb).symm)

theorem SampledLevel.endpoint_critical_guard
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (S :SampledLevel old hv hd left right R side pMID pChild)
    (b :ℕ) (hb0 :beginBirth old≤b) (hb1 :b<midpointBirth old hv hd left right R)
    (hb :FormulaSignSlotRadialProviderAtomic.Active (CTX r) b) :
    IntegralFramedPhysicalCompanionPoint.scalarValue BK T FormulaSignSlotRadialProviderAtomic.bank_represents
      (CTX r) S.receipt.word b=InfinitesimalSign.encode 0:=by
  let i:=beginBirth old+R.result.commands.length-1-b
  have HI:i<R.result.commands.length:=by unfold midpointBirth at hb1;dsimp only [i];omega
  have HB:(birth i)=b:=by unfold endpointBirth;dsimp only [i];unfold midpointBirth at hb1;omega
  obtain ⟨A,E,ordinal,HE,N⟩:=S.physical
  have HV:∀j :Fin ((oldCs).length+R.result.commands.length+1+K+1+K),
      (C).point S.localTuple j.val=IntegralMixedChronologicalLevelScalarValues.levelValues
        pMID pChild R.result.nextValues g js j:=N.bank_values
  have HG:=S.receipt.endpoint_native_critical_guard old hv hd left right R side ordinal HE N.pair_raw
    pMID pChild HV N.endpoint_trace i HI (by simpa only [HB] using hb)
  simpa only [HB] using HG

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
