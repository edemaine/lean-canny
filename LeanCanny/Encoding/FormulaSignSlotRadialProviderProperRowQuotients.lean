/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowValue
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowRuling
public import LeanCanny.Encoding.IntegralFramedPhysicalBankShift
/-! # Both statistic interpretations retain the original actual bank quotients -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "I"=>IntegralFramedPhysicalSquare.input P D H L F C hs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family originalValue
  IntegralMixedFramedHistoryScript.run IntegralMixedHistory.reframe

noncomputable def Interprets (mean : Bool) (z w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (I (terminal mean) (positive mean)) z w)
    (hfit : (G).birth (parentKey mean z)≤(G).birth (terminal mean z))
    (φ : ((G).state (parentKey mean z)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) : Prop :=
  ∀i,φ (((G).state (parentKey mean z)).sampler.scalarPrefix.basis.generator i)=
    IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs (terminal mean) (positive mean) z w hw
      (embed hfit i)^weights ((G).cap (parentKey mean z)) (2^(G).width (parentKey mean z))
        ((G).birth (parentKey mean z)) i

theorem parent_birth_actual (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :
    (G).birth (parentKey mean z)=creating z :=
  (IntegralMixedFramedHistoryFamilyBits.family_birth P D H _).trans
    (parentKey_prefix mean z (row_count_positive z hv))

private theorem same_root (mean : Bool) (z : List Bool) :
    pairFst (terminal mean z)=pairFst (parentKey mean z) :=by
  rw [parentKey_root]
  have HE:=FormulaSignSlotRadialProviderFieldEquality.key_root (context mean z)
  simpa only [terminal,Function.comp_apply,context,pairFst_pair] using HE

theorem quotients_original (mean right : Bool) (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HL : u∈FormulaSignSlotRadialProviderProperRowWitness.language right)
    (hw : SquareSampleCompleteVertices.Valid (I (terminal mean) (positive mean))
      (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord mean u))
    (hfit : (G).birth (parentKey mean (FormulaSignSlotRadialProviderProperRowWitness.key u))≤
      (G).birth (terminal mean (FormulaSignSlotRadialProviderProperRowWitness.key u)))
    (φ : ((G).state (parentKey mean (FormulaSignSlotRadialProviderProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : Interprets mean (FormulaSignSlotRadialProviderProperRowWitness.key u)
      (FormulaSignSlotRadialProviderProperRowWitness.ownWord mean u) hw hfit φ) :
    ∀i : Fin ((G).birth (parentKey mean (FormulaSignSlotRadialProviderProperRowWitness.key u))),
      φ (((G).state (parentKey mean (FormulaSignSlotRadialProviderProperRowWitness.key u))).bank.numerator i)/
      (((G).state (parentKey mean (FormulaSignSlotRadialProviderProperRowWitness.key u))).bank.denominator i:ℝ)=
      originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv
        ((G).birth (parentKey mean (FormulaSignSlotRadialProviderProperRowWitness.key u))-1-i.val) :=by
  intro i
  let z:=FormulaSignSlotRadialProviderProperRowWitness.key u
  let old:=parentKey mean z
  have HB : (G).birth old=creating z:=parent_birth_actual mean z hv
  have HQ:=IntegralFramedPhysicalBankShift.values_of_interpretation P D H L F C hs
    (terminal mean) (positive mean) z (FormulaSignSlotRadialProviderProperRowWitness.ownWord mean u) hw
    old (same_root mean z) hfit φ hφ i
  let p:=(G).birth old-1-i.val
  have HP : p<creating z:=by
    dsimp only [p,old,z]
    dsimp only [old,z] at HB
    have HI:=i.isLt
    omega
  have HFIT : creating z≤(G).birth (terminal mean z):=HB ▸ hfit
  have HV:=native_scalar_value mean right u hv HL hw p HP HFIT
  have HP0 : p<(G).birth (terminal mean z):=HP.trans_le HFIT
  have HE : embed hfit i=⟨(G).birth (terminal mean z)-1-p,by
      change (G).birth (terminal mean z)-1-p<(G).birth (terminal mean z)
      omega⟩:=by
    apply Fin.ext
    dsimp only [embed,Fin.val_mk,p,old,z]
    have HI:=i.isLt
    omega
  have HPoint:=congrArg (IntegralFramedPhysicalSquare.point P D H L F C hs
    (terminal mean) (positive mean) z (FormulaSignSlotRadialProviderProperRowWitness.ownWord mean u) hw) HE
  exact HQ.trans (HPoint.trans HV)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
