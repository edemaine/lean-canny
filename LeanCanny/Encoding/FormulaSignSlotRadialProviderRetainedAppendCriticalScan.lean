/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendCorrelation
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPaddingReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPacket
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPastCritical
/-! # The fresh retained word satisfies the entire actual native critical scan -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
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
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentState parentTuple parentValues parentHom parentCommands parentDescriptor

private theorem critical_packet (c w : List Bool) :
    LeanCanny.pair c w∈FormulaSignSlotRadialProviderAtomic.criticalLanguage ↔
      SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input c w ∧
        IntegralFramedPhysicalCriticalGuardScan.holds FormulaSignSlotRadialProviderAtomic.input
          (B).parameters (B).plan (B).data T (B).nodes (B).factor (B).seed (B).bounds (B).key
          FormulaSignSlotRadialProviderAtomic.critical_count (LeanCanny.pair c w) := by
  simp only [FormulaSignSlotRadialProviderAtomic.criticalLanguage,IntegralFramedPhysicalCriticalGuardScan.language,
    Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]

theorem WordReceipt.all_critical
    {old : List Bool} {hv : A old} {hd : depth old<dimension old}
    {e : ℕ} {he : e<endBirth (dimension old) (N old) old}
    {p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ} (W : WordReceipt old hv hd e he p) :
    FormulaSignSlotRadialProviderAtomic.CriticalScan (packet (dimension old) old e W.word) := by
  change FormulaSignSlotRadialProviderAtomic.sampleQuery (packet (dimension old) old e W.word)∈
    FormulaSignSlotRadialProviderAtomic.criticalLanguage
  rw [sample_query_packet,critical_packet]
  refine ⟨W.valid,?_⟩
  apply critical_holds B T FormulaSignSlotRadialProviderAtomic.bank_represents
    FormulaSignSlotRadialProviderAtomic.critical_count (C (preparedRoot old e)) W.word W.valid
  intro b hb ha
  have HB : b<fullBirth old e := hb.trans_eq (FormulaSignSlotRadialProviderRecordPrefix.full_prefix _)
  by_cases HPast : b<N old+start old
  · exact past_critical old hv hd e he W.word W.valid W.old_raw_native b HPast ha
  apply (FormulaSignSlotRadialProviderAtomic.scalarValue_zero_iff_field
    (C (preparedRoot old e)) W.word W.valid b ha).mpr
  by_cases HLocal : b<finishBirth old e
  · rw [W.local_geometric_point b (by omega) HLocal]
    exact W.local_correlation b (by omega) HLocal
  · have HAfter : finishBirth old e≤b := by omega
    rw [W.padding_geometric_point b HAfter HB]
    have HS := (seed_metadata_after_finish old hv hd e he b HAfter HB).2
    exact (W.padding_field b HAfter HB).trans
      (nativePoint_value old e W.paddingPoint
        ⟨FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old e)) b,
          FormulaSignSlotRadialProviderAtomic.selected_lt _ _ ha⟩ 0 HS).symm

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
