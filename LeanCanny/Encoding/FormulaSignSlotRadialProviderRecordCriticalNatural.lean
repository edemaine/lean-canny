/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicPointLanguage
/-! # Provider critical guards read their actual retained natural columns -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem block_natural (b : IntegralFramedBankQuery.Bank) (tab : IntegralMixedHeaderTablesBits.Tables)
    (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input b) c w)
    (birth i : ℕ)
    (hc : IntegralMixedFramedPhysicalIndex.prefixArity b.parameters tab
      (pair (b.key c) (List.replicate birth true))+i<(IntegralFramedPhysicalBankTerm.input b).count c) :
    IntegralFramedPhysicalCompanionPoint.block b tab c w hw birth i=
      bankNatural b c w hw
        (IntegralMixedFramedPhysicalIndex.prefixArity b.parameters tab
          (pair (b.key c) (List.replicate birth true))+i)^
        IntegralMixedFramedCriticalGuardBits.physicalPower b.parameters b.key (fun _=>birth) c := by
  unfold IntegralFramedPhysicalCompanionPoint.block
  rw [dite_eq_left hc]
  apply congrArg (fun x : ℝ=>x^IntegralMixedFramedCriticalGuardBits.physicalPower b.parameters b.key (fun _=>birth) c)
  exact (IntegralFramedPhysicalSquare.naturalPoint_at b.parameters b.plan b.data
    b.nodes b.factor b.seed b.bounds b.key b.positive c w hw
    ⟨IntegralMixedFramedPhysicalIndex.prefixArity b.parameters tab
      (pair (b.key c) (List.replicate birth true))+i,hc⟩).symm

private theorem scalarValue_of_scan (b : IntegralFramedBankQuery.Bank) (tab : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents b.parameters b.plan b.data tab) (c w : List Bool)
    (h : pair c w∈IntegralFramedPhysicalCriticalGuardScan.language (IntegralFramedPhysicalBankTerm.input b)
      b.parameters b.plan b.data tab b.nodes b.factor b.seed b.bounds b.key
      (IntegralFramedPhysicalCompanionPoint.count_eq b tab hr))
    (i : ℕ) (hi : i<IntegralMixedFramedHistoryFamilyBits.prefixLength b.parameters (b.key c)) :
    IntegralFramedPhysicalCompanionPoint.scalarValue b tab hr c w i=InfinitesimalSign.encode 0 := by
  exact h.2 i (by simpa only [pairFst_pair] using hi)

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedPhysicalIndex.prefixArity UniformIntegralPowerSchedule.physical

theorem scalarValue_of_valid (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (b : ℕ) (hb : b<IntegralMixedFramedHistoryFamilyBits.prefixLength P
      ((B).key (FormulaSignSlotRadialProviderAtomic.context q))) :
    IntegralFramedPhysicalCompanionPoint.scalarValue B T FormulaSignSlotRadialProviderAtomic.bank_represents
      (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q) b=
      InfinitesimalSign.encode 0 := by
  apply scalarValue_of_scan B T FormulaSignSlotRadialProviderAtomic.bank_represents
    (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q) ?_ b hb
  exact FormulaSignSlotRadialProviderAtomic.valid_critical q hv

theorem selected_column_lt (r : List Bool) (b : ℕ)
    (hb : FormulaSignSlotRadialProviderAtomic.Active (context r) b) :
    IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (context r)) (List.replicate b true))+
      FormulaSignSlotRadialProviderAtomic.selected (context r) b<
        FormulaSignSlotRadialProviderAtomic.input.count (context r) := by
  have H := IntegralMixedFramedCriticalGuardBits.physical_lt P (B).plan (B).data T
    FormulaSignSlotRadialProviderAtomic.bank_represents
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
    (pair (context r) (List.replicate b true)) hb
  have HC := IntegralFramedPhysicalCompanionPoint.count_eq B T
    FormulaSignSlotRadialProviderAtomic.bank_represents (context r) (List.replicate b true)
  have HE : IntegralMixedFramedCriticalGuardBits.physical P T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
      (pair (context r) (List.replicate b true))=
        IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (context r)) (List.replicate b true))+
          FormulaSignSlotRadialProviderAtomic.selected (context r) b := by
    simp only [FormulaSignSlotRadialProviderAtomic.selected,IntegralFramedPhysicalCompanionPoint.selected,
      IntegralMixedFramedCriticalGuardBits.physical,IntegralMixedFramedCriticalGuardBits.packet,
      IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
      pairFst_pair,pairSnd_pair,List.length_replicate,Nat.add_assoc]
  rw [←HE]
  exact H.trans_eq HC

theorem scalarValue_zero_iff_natural (r w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context r) w)
    (b : ℕ) (hb : FormulaSignSlotRadialProviderAtomic.Active (context r) b) :
    IntegralFramedPhysicalCompanionPoint.scalarValue B T FormulaSignSlotRadialProviderAtomic.bank_represents
      (context r) w b=InfinitesimalSign.encode 0 ↔
    FormulaSignSlotRadialProviderAtomic.bankField (context r) w hw b=
      natural r w hw
        (IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (context r)) (List.replicate b true))+
          FormulaSignSlotRadialProviderAtomic.selected (context r) b)^
        UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b := by
  have H := FormulaSignSlotRadialProviderAtomic.scalarValue_zero_iff_field (context r) w hw b hb
  change _ ↔ _=IntegralFramedPhysicalCompanionPoint.block B T (context r) w hw b
    (FormulaSignSlotRadialProviderAtomic.selected (context r) b) at H
  rw [block_natural B T (context r) w hw b _ (selected_column_lt r b hb)] at H
  have HP : IntegralMixedFramedCriticalGuardBits.physicalPower P (B).key (fun _=>b) (context r)=
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b := by
    unfold IntegralMixedFramedCriticalGuardBits.physicalPower
    rw [key_root]
  rw [HP] at H
  exact H

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
