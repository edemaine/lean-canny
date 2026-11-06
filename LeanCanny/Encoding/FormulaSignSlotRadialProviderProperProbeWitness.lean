/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbeValues
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCoordinateSearch
/-! # Independent fresh provider statistic words share the original fields -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem family_width (p : IntegralCriticalHistoryTask.Parameters)
    (d : IntegralMixedFramedHistoryFamilyBits.Plan p) (h : IntegralMixedFramedHistoryFamilyBits.Data p d)
    (key : List Bool) : (IntegralMixedFramedHistoryFamilyBits.family p d h).width key=p.width (pairFst key) :=rfl
private theorem planned_width (p : IntegralCriticalHistoryTask.Parameters)
    (l f c : List Bool→ℕ) (key : List Bool) :
    (IntegralMixedFramedNormalizationBits.planned p l f c).width key=p.width key :=rfl
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family

theorem probe_parent_width (mean : Bool) (z : List Bool) :
    (G).width (parentKey mean z)=FormulaSignSlotRadialProviderAtomic.width (atomic z) :=by
  rw [family_width,parentKey_root]
  have HE:=FormulaSignSlotRadialProviderRecordPrefix.width (root mean z)
    (FormulaSignSlotRadialProviderAtomic.root (atomic z))
    ((root_provider mean z).trans (FormulaSignSlotRadialProviderAtomic.root_provider (atomic z)).symm)
  simpa only [FormulaSignSlotRadialProviderRecordPlan.bank,FormulaSignSlotRadialProviderAtomic.width,
    FormulaSignSlotRadialProviderRecordPlan.certifiedParameters,planned_width] using HE

theorem exists_own_words (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    ∃ordinary mean,
      ordinary.length=FormulaSignSlotRadialProviderProperCoordinateSearch.fullWidth false z ∧
      mean.length=FormulaSignSlotRadialProviderProperCoordinateSearch.fullWidth true z ∧
      SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context false z) ordinary ∧
      SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context true z) mean ∧
      ∀rank,FormulaSignSlotRadialProviderProperRowWitness.fieldMatch false
          (FormulaSignSlotRadialProviderProperRowWitness.packet z ordinary mean rank)∈
          FormulaSignSlotRadialProviderFieldEqualityList.language ∧
        FormulaSignSlotRadialProviderProperRowWitness.fieldMatch true
          (FormulaSignSlotRadialProviderProperRowWitness.packet z ordinary mean rank)∈
          FormulaSignSlotRadialProviderFieldEqualityList.language :=by
  obtain ⟨ordinary,hO,HOL,HO⟩:=exists_probe_fields false z hv hg
  obtain ⟨mean,hM,HML,HM⟩:=exists_probe_fields true z hv hg
  refine ⟨ordinary,mean,HOL,HML,hO,hM,fun rank=>?_⟩
  constructor
  · simpa only [FormulaSignSlotRadialProviderProperRowWitness.fieldMatch,
      FormulaSignSlotRadialProviderProperRowWitness.packet,FormulaSignSlotRadialProviderProperRowWitness.atomic,
      FormulaSignSlotRadialProviderProperRowWitness.key,FormulaSignSlotRadialProviderProperRowWitness.ownWord,
      pairFst_pair,pairSnd_pair,Bool.false_eq_true,ite_false,initial,oldPacket]
      using probe_field_list false z hv ordinary hO HO
  · simpa only [FormulaSignSlotRadialProviderProperRowWitness.fieldMatch,
      FormulaSignSlotRadialProviderProperRowWitness.packet,FormulaSignSlotRadialProviderProperRowWitness.atomic,
      FormulaSignSlotRadialProviderProperRowWitness.key,FormulaSignSlotRadialProviderProperRowWitness.ownWord,
      pairFst_pair,pairSnd_pair,ite_true,initial,oldPacket]
      using probe_field_list true z hv mean hM HM

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
