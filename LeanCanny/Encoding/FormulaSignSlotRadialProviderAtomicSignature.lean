/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicOccurrence
/-! # Every provider signature producer reads the same actual atomic point -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank

theorem signature_readback (q : List Bool) (hv : Valid q)
    (i : Fin ((P).ambient (pairFst ((B).key (context q)))+1)) :
    field q hv (Nat.fromBitsLE (WordList.get (signature (dimension q) (initial q) q) i.val))=point q hv i := by
  have HIn : i.val<dimension q+1 := by rw [←native_dimension q]; exact i.isLt
  have HL := IntegralMixedChronologicalPointSignatureCode.code_lookup (dimension q)
    (first (dimension q) (initial q) q) (frozen q) ⟨i.val,HIn⟩
  change Nat.fromBitsLE (WordList.get (signature (dimension q) (initial q) q) i.val)=_ at HL
  rw [HL]
  by_cases hi : i.val<depth q
  · have HI : i.val<WordListRecords.count (frozen q) := by rw [frozen_count]; exact hi
    rw [IntegralMixedChronologicalPointSignatureCode.producer,ite_eq_left HI]
    exact ((occurrence q hv).frozen i hi).symm
  · let j := dimension q-i.val
    have HD := depth_le q (valid_grammar q hv)
    have HJ : j<free (dimension q) q := by change j<dimension q+1-depth q; unfold j; omega
    obtain ⟨HB,_,HR⟩ := companions q hv j HJ
    have HS : selected (context q) (first (dimension q) (initial q) q+j)=i.val := by
      rw [capture_selected q hv j HJ]
      unfold j
      omega
    have HE : IntegralMixedChronologicalPointSignatureCode.producer (dimension q)
        (first (dimension q) (initial q) q) (frozen q) i.val=first (dimension q) (initial q) q+j := by
      unfold IntegralMixedChronologicalPointSignatureCode.producer
      rw [frozen_count,ite_eq_right hi]
      unfold j
      omega
    rw [HE]
    have HF : (⟨selected (context q) (first (dimension q) (initial q) q+j),selected_lt _ _ HB⟩ :
        Fin ((P).ambient (pairFst ((B).key (context q)))+1))=i := Fin.ext HS
    rw [HF] at HR
    exact HR

theorem signature_bounded (q : List Bool) (hv : Valid q)
    (i : Fin ((P).ambient (pairFst ((B).key (context q)))+1)) :
    Nat.fromBitsLE (WordList.get (signature (dimension q) (initial q) q) i.val)<
      IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (context q)) := by
  have HIn : i.val<dimension q+1 := by rw [←native_dimension q]; exact i.isLt
  have HL := IntegralMixedChronologicalPointSignatureCode.code_lookup (dimension q)
    (first (dimension q) (initial q) q) (frozen q) ⟨i.val,HIn⟩
  change Nat.fromBitsLE (WordList.get (signature (dimension q) (initial q) q) i.val)=_ at HL
  rw [HL]
  change IntegralMixedChronologicalPointSignatureCode.producer (dimension q)
    (first (dimension q) (initial q) q) (frozen q) i.val<_
  unfold IntegralMixedChronologicalPointSignatureCode.producer
  rw [frozen_count]
  split_ifs with hi
  · have HH := (own_frame_good q hv).2 i.val (by rw [frozen_count]; exact hi)
    have HB := (IntegralFramedPhysicalCompanionPoint.active_direct B T
      (context q) (ownBirth q) (own_active q hv)).1
    exact HH.trans HB
  · let j := dimension q-i.val
    have HD := depth_le q (valid_grammar q hv)
    have HJ : j<free (dimension q) q := by change j<dimension q+1-depth q; unfold j; omega
    obtain ⟨HB,_,_⟩ := companions q hv j HJ
    have HT := (IntegralFramedPhysicalCompanionPoint.active_direct B T (context q)
      (first (dimension q) (initial q) q+j) HB).1
    have HE : first (dimension q) (initial q) q+(dimension q+1-depth q)-1-(i.val-depth q)=
        first (dimension q) (initial q) q+j := by unfold j; omega
    rw [HE]
    exact HT

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
