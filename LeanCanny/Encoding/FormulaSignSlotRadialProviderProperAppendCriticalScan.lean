/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendCorrelation
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPaddingPhysical
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPastGuards
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendEndpointWordCriticalGuard
/-! # Every native critical test holds on the one actual proper-child word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem inactive_scalar (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (hT : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (b : ℕ) (hb : ¬IntegralFramedPhysicalCompanionPoint.Active B T c b) :
    IntegralFramedPhysicalCompanionPoint.scalarValue B T hT c w b=InfinitesimalSign.encode 0 := by
  have HP := IntegralFramedPhysicalCriticalGuardTest.packet (IntegralFramedPhysicalBankTerm.input B)
    B.parameters B.plan B.data T B.nodes B.factor B.seed B.bounds B.key
    IntegralFramedPhysicalCriticalGuardScan.stage (IntegralFramedPhysicalCompanionPoint.count_eq B T hT)
    c w (List.replicate b true) hw
  change IntegralFramedPhysicalCompanionPoint.scalarValue B T hT c w b=InfinitesimalSign.encode (SignType.sign
    ((IntegralMixedFramedCriticalGuardBits.polynomial B.parameters B.plan B.data T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum B.key) IntegralFramedPhysicalCriticalGuardScan.stage
      (LeanCanny.pair c (List.replicate b true))).eval₂ (Int.castRingHom ℝ)
        (IntegralFramedPhysicalCompanionPoint.fullTuple B T hT c w hw b))) at HP
  have HN : ¬IntegralMixedFramedCriticalGuardBits.Active B.parameters T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum B.key) IntegralFramedPhysicalCriticalGuardScan.stage
      (LeanCanny.pair c (List.replicate b true)) := hb
  rw [IntegralMixedFramedCriticalGuardBits.polynomial,ite_eq_right HN,MvPolynomial.eval₂_zero,sign_zero] at HP
  exact HP

private theorem critical_holds (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (hT : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (hc : ∀c d,IntegralMixedFramedCriticalGuardBits.count B.parameters T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum B.key) (LeanCanny.pair c d)=
        (IntegralFramedPhysicalBankTerm.input B).count c)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (h : ∀b,b<prefixLength B.parameters (B.key c)→IntegralFramedPhysicalCompanionPoint.Active B T c b→
      IntegralFramedPhysicalCompanionPoint.scalarValue B T hT c w b=InfinitesimalSign.encode 0) :
    IntegralFramedPhysicalCriticalGuardScan.holds (IntegralFramedPhysicalBankTerm.input B) B.parameters B.plan
      B.data T B.nodes B.factor B.seed B.bounds B.key hc (LeanCanny.pair c w) := by
  simp only [IntegralFramedPhysicalCriticalGuardScan.holds,pairFst_pair]
  change ∀b,b<prefixLength B.parameters (B.key c)→
    IntegralFramedPhysicalCompanionPoint.scalarValue B T hT c w b=InfinitesimalSign.encode 0
  intro b hb
  by_cases ha : IntegralFramedPhysicalCompanionPoint.Active B T c b
  · exact h b hb ha
  · exact inactive_scalar B T hT c w hw b ha

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor

private theorem critical_packet (c w : List Bool) :
    LeanCanny.pair c w∈FormulaSignSlotRadialProviderAtomic.criticalLanguage ↔
      SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input c w ∧
        IntegralFramedPhysicalCriticalGuardScan.holds FormulaSignSlotRadialProviderAtomic.input
          (B).parameters (B).plan (B).data T (B).nodes (B).factor (B).seed (B).bounds (B).key
          FormulaSignSlotRadialProviderAtomic.critical_count (LeanCanny.pair c w) := by
  simp only [FormulaSignSlotRadialProviderAtomic.criticalLanguage,IntegralFramedPhysicalCriticalGuardScan.language,
    Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]

private theorem padding_point_value (root : List Bool) (p0 : Fin ((P).ambient root+1)→ℝ)
    (i : Fin ((B).parameters.ambient (pairFst ((B).key (C root)))+1)) (j : Fin ((P).ambient root+1))
    (h : i.val=j.val) : nativePaddingPoint root p0 i=p0 j := by
  unfold nativePaddingPoint
  apply congrArg p0
  apply Fin.ext
  simpa only [Fin.val_cast] using h

theorem SampledLevel.all_critical
    {old : List Bool} {hv : A old} {hd : depth old<dimension old}
    {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
    {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
      (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
    (S : SampledLevel old hv hd left right R side pMID pChild) :
    FormulaSignSlotRadialProviderAtomic.CriticalScan
      (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word) := by
  change FormulaSignSlotRadialProviderAtomic.sampleQuery
    (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word)∈
      FormulaSignSlotRadialProviderAtomic.criticalLanguage
  rw [sample_query_packet,critical_packet]
  refine ⟨S.receipt.valid,?_⟩
  apply critical_holds B T FormulaSignSlotRadialProviderAtomic.bank_represents
    FormulaSignSlotRadialProviderAtomic.critical_count
    (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid
  intro b hb ha
  have HB : b<fullBirth old hv hd left right R side :=
    hb.trans_eq (FormulaSignSlotRadialProviderRecordPrefix.full_prefix _)
  by_cases HPast : b<beginBirth old
  · exact S.past_critical b (HPast.trans_eq (begin_eq_start old)) ha
  by_cases HE : b<midpointBirth old hv hd left right R
  · exact S.endpoint_critical_guard old hv hd left right R side b (by omega) HE ha
  apply (FormulaSignSlotRadialProviderAtomic.scalarValue_zero_iff_field
    (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid b ha).mpr
  by_cases HLocal : b<finishBirth old hv hd left right R side
  · rw [S.local_geometric_point old hv hd left right R side b (by omega) HLocal]
    exact S.local_correlation b (by omega) HLocal
  · have HAfter : finishBirth old hv hd left right R side≤b := by omega
    rw [S.padding_geometric_point old hv hd left right R side b HAfter HB]
    have HS := (seed_metadata_after_finish old hv hd left right R side b HAfter HB).2
    exact (S.receipt.padding_field b HAfter HB).trans
      (padding_point_value (preparedRoot old R.leftSpec R.rightSpec side) S.paddingPoint
        ⟨FormulaSignSlotRadialProviderAtomic.selected
          (C (preparedRoot old R.leftSpec R.rightSpec side)) b,
          FormulaSignSlotRadialProviderAtomic.selected_lt _ _ ha⟩ 0 HS).symm

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
