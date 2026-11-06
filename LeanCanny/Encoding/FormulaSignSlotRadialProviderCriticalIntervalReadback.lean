/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
/-! # Literal strict-interval sign readback for the appended probe -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (birth key input)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "hr" => FormulaSignSlotRadialProviderAtomic.bank_represents
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
 FormulaSignSlotRadialProviderRecordPlan.tables IntegralMixedFramedHistoryFamilyBits.family

theorem value_packet (upper : Bool) (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q v) :
    value upper (pair q v)=InfinitesimalSign.encode
      (SignType.sign ((term upper (IntegralMixedPhysicalCriticalQuery.root q)).eval
        (IntegralFramedPhysicalBankTerm.env (childBank)
          T hr q v hv))) :=by
  have HP:=IntegralFramedPhysicalBankTerm.packet (childBank)
    T hr q v hv (word upper) []
  simpa only [value,Function.comp_apply,probe,IntegralMixedFramedBankTermBits.source,
    RationalSubstitutionBits.Source.syntax,RationalSubstitutionBits.Source.ofTerm,
    IntegralMixedFramedBankTermBits.wordAt,word,TermView.term_toBits,childBank,withKeyBank,key,
    IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair] using HP

theorem interval_iff (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q v)
    (hg : Guard q) :
    (value false (pair q v)=InfinitesimalSign.encode 1 ∧
      value true (pair q v)=InfinitesimalSign.encode 1) ↔
    (let env:=IntegralFramedPhysicalBankTerm.env (childBank)
      T hr q v hv
     env (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.leftWord q))<env (birth false q) ∧
      env (birth false q)<env (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.rightWord q))) :=by
  rw [value_packet false q v hv,value_packet true q v hv]
  have HB : FormulaSignSlotRadialProviderCriticalPrefixes.birth false
      (pair (IntegralMixedPhysicalCriticalQuery.root q) [])=birth false q :=by
    simp only [FormulaSignSlotRadialProviderCriticalPrefixes.birth,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]
  have HL : IntegralMixedPhysicalCriticalQuery.leftWord (pair (IntegralMixedPhysicalCriticalQuery.root q) [])=
      IntegralMixedPhysicalCriticalQuery.leftWord q :=by
    simp only [IntegralMixedPhysicalCriticalQuery.leftWord,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]
  have HR : IntegralMixedPhysicalCriticalQuery.rightWord (pair (IntegralMixedPhysicalCriticalQuery.root q) [])=
      IntegralMixedPhysicalCriticalQuery.rightWord q :=by
    simp only [IntegralMixedPhysicalCriticalQuery.rightWord,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]
  simp only [term,Bool.false_eq_true,ite_false,ite_true,clipped,endpoint,
    HB,HL,HR,
    min_eq_left hg.2.1.le,min_eq_left hg.2.2.le,Term.eval,Int.cast_neg,Int.cast_one,
    neg_one_mul,SquareSampleTestSign.encode_eq_iff,sign_eq_one_iff,←sub_eq_add_neg,sub_pos]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
