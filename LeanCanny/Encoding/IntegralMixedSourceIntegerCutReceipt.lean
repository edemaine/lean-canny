/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutCreationInstruction
public import LeanCanny.Encoding.IntegralMixedSourceIntegerLastCode
/-! # Literal final original code binds the actual full selected-factor receipt -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerCutReceipt
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits
open IntegralMixedFramedHistoryFamilyBits (Plan family instruction)
open IntegralMixedCutCreationReceipt
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem stateView_common (A : Parameters) (E : Plan A) (J : IntegralMixedFramedHistoryFamilyBits.Data A E) (key : List Bool) :
    commonDenominator (IntegralMixedFramedFamilyRunView.stateView A E J key)=
      commonDenominator (IntegralMixedFramedFamilyRunView.familyRun A E key):=rfl

private theorem family_snapshot (A : Parameters) (E : Plan A) (J : IntegralMixedFramedHistoryFamilyBits.Data A E) (key : List Bool) :
    IntegralMixedPrefixSnapshot.ofState ((family A E J).state key)=
      IntegralMixedPrefixSnapshot.ofState (reframe (IntegralMixedFramedFamilyRunView.familyRun A E key)
        (instruction A E key).source (instruction A E key).source_cap):=rfl

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
 (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
 (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
 (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
 (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
 (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
local notation "D"=>IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom
variable (H : IntegralMixedFramedHistoryFamilyBits.Data P (IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom))
 (key : List Bool) (codes : List (List Bool)) (code labels : List Bool) (values : ℕ→ℝ) (a : ℝ)
 (htable : IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode (codes++[code]))
 (hk : IntegralMixedFramedHistoryFamilyBits.prefixLength P key=N (pairFst key)+codes.length)

include H htable hk in
theorem instruction_record :instruction P D key=
    instantiate (IntegralMixedFramedFamilyRunView.familyRun P D key)
      (IntegralMixedCausalUnitRecordBits.record (S (pairFst key) (N (pairFst key)+codes.length)) (hn _)
        (N (pairFst key)+codes.length) code (by rw [hd];exact hcap _)):=by
 have HI:=IntegralMixedSourceIntegerLastCode.last_instruction P S hn hd hcap N T hz hT hroom H key codes code htable hk
 unfold IntegralMixedSourceIntegerRecordAppend.step at HI
 rw [IntegralMixedSourceIntegerLastCode.code_last _ codes code htable] at HI
 exact HI.trans (instantiate_congr _ _ _ (stateView_common P D H key))

include htable hk in
theorem native_receipt
    (hcoded : (IntegralMixedPrefixSnapshot.ofState ((family P D H).state key)).CodedFactor labels values a code) :
    atKey P D H key=some (native P D H key) ∧ (native P D H key).HasRoot values a:=by
 let raw:=IntegralMixedFramedFamilyRunView.familyRun P D key
 let Q:=S (pairFst key) (N (pairFst key)+codes.length)
 let originalRecord:=IntegralMixedCausalUnitRecordBits.record Q (hn _) (N (pairFst key)+codes.length) code
   (by dsimp only [Q];rw [hd];exact hcap _)
 have HI:=instruction_record P S hn hd hcap N T hz hT hroom H key codes code htable hk
 have HS:=congrArg (fun i : Instruction (P.ambient (pairFst key)) (P.width (pairFst key))=>
   IntegralMixedPrefixSnapshot.ofState (reframe raw i.source i.source_cap)) HI
 have HSS:=(family_snapshot P D H key).trans HS
 have HC : (IntegralMixedPrefixSnapshot.ofState (reframe raw Q originalRecord.source_cap)).CodedFactor labels values a code:=
   (congrArg (fun d : IntegralMixedPrefixSnapshot.Data=>d.CodedFactor labels values a code) HSS).mp hcoded
 have HB : (IntegralMixedFramedHistoryFamilyBits.commands P D key).length=N (pairFst key)+codes.length:=
   (paddedPast_length _ _ _).trans hk
 have HP:=coded_instruction raw Q (hn _) originalRecord.source_cap labels values a code
   (by dsimp only [Q];rw [hd];exact hcap _) HC
 have HE :instantiate raw originalRecord=instantiate raw
     (IntegralMixedCausalUnitRecordBits.record Q (hn _) (IntegralMixedFramedHistoryFamilyBits.commands P D key).length code
       (by dsimp only [Q];rw [hd];exact hcap _)):=
   congrArg (fun b : ℕ=>instantiate raw (IntegralMixedCausalUnitRecordBits.record Q (hn _) b code
     (by dsimp only [Q];rw [hd];exact hcap _))) HB.symm
 rw [←HE] at HP
 obtain ⟨receipt,hr,ha⟩:=HP
 have HK :atKey P D H key=some receipt:=
   (congrArg (ofInstruction raw) HI).trans hr
 have HEq:=atKey_some_native P D H key receipt HK
 exact ⟨HK.trans (congrArg some HEq),(congrArg (fun r : IntegralMixedCutCreationReceipt.Data=>r.HasRoot values a) HEq).mp ha⟩

include htable hk in
theorem native_root
    (hcoded : (IntegralMixedPrefixSnapshot.ofState ((family P D H).state key)).CodedFactor labels values a code) :
    (native P D H key).HasRoot values a:=
 (native_receipt P S hn hd hcap N T hz hT hroom H key codes code labels values a htable hk hcoded).2

end LeanCanny.Encoding.IntegralMixedSourceIntegerCutReceipt
