/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordReadback
public import LeanCanny.Algebra.IntegralMixedFramedHistorySuccessor
public import LeanCanny.Algebra.IntegralMixedFramedFamilyRunView
/-! # The last raw code is the actual last current-Q instruction

The raw table is chronological. Its final word is instantiated against the
same prepared root's older prefix; no command-list equality is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerLastCode
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem count_last (root : List Bool) (oldCodes : List (List Bool)) (code : List Bool)
    (h : IntegralMixedCausalRecordPlanBits.records root=WordList.encode (oldCodes++[code])) :
    IntegralMixedCausalRecordPlanBits.count root=oldCodes.length+1:=by
 simp only [IntegralMixedCausalRecordPlanBits.count,h,WordListRecords.count_encode,List.length_append,
   List.length_singleton]

theorem code_last (root : List Bool) (oldCodes : List (List Bool)) (code : List Bool)
    (h : IntegralMixedCausalRecordPlanBits.records root=WordList.encode (oldCodes++[code])) :
    IntegralMixedCausalRecordPlanBits.code root oldCodes.length=code:=by
 simp only [IntegralMixedCausalRecordPlanBits.code,h,WordList.get_encode,List.getElem?_append_right (le_refl _),
   Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
 (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
 (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
 (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
 (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
 (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
local notation "D"=>IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom

theorem rules_length_last (root : List Bool) (oldCodes : List (List Bool)) (code : List Bool)
    (h : IntegralMixedCausalRecordPlanBits.records root=WordList.encode (oldCodes++[code])) :
    ((D).rules root).length=N root+oldCodes.length+1:=by
 unfold IntegralMixedSourceIntegerRecordAppend.plan
 rw [IntegralMixedSourceIntegerPrelude.extended_length,IntegralMixedSourceIntegerRecordAppend.later_length,
   count_last root oldCodes code h]
 omega

include hroom in
theorem parent_bound (root : List Bool) (oldCodes : List (List Bool)) (code : List Bool)
    (h : IntegralMixedCausalRecordPlanBits.records root=WordList.encode (oldCodes++[code])) :
    N root+oldCodes.length≤P.cap root+1:=by
 have H:=hroom root
 rw [count_last root oldCodes code h] at H
 omega

include hroom in
theorem parent_key_prefix (root aux : List Bool) (oldCodes : List (List Bool)) (code : List Bool)
    (h : IntegralMixedCausalRecordPlanBits.records root=WordList.encode (oldCodes++[code])) :
    prefixLength P (keyAt root (N root+oldCodes.length) aux)=N root+oldCodes.length:=
 keyAt_prefix P root _ aux (parent_bound P N hroom root oldCodes code h)

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan

variable (H : IntegralMixedFramedHistoryFamilyBits.Data P (IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom)) (key : List Bool) (oldCodes : List (List Bool)) (code : List Bool)
 (h : IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode (oldCodes++[code]))
 (hk : prefixLength P key=N (pairFst key)+oldCodes.length)

include H h hk in
theorem last_instruction : instruction P D key=instantiate (IntegralMixedFramedFamilyRunView.stateView P D H key)
    (IntegralMixedSourceIntegerRecordAppend.step P S hn hd hcap N (pairFst key) oldCodes.length):=
 IntegralMixedSourceIntegerRecordAppend.instruction_at_bank P S hn hd hcap N T hz hT hroom H key oldCodes.length
   (by rw [count_last _ oldCodes code h];omega) hk

include h hk in
theorem rules_last : (D).rules (pairFst key)=instruction P D key::commands P D key:=by
 have HL : ((D).rules (pairFst key)).length=prefixLength P key+1:=by
   rw [rules_length_last P S hn hd hcap N T hz hT hroom _ oldCodes code h,hk]
 have HE:=paddedPast_succ (defaultInstruction P D (pairFst key)) ((D).rules (pairFst key)) (prefixLength P key)
 rw [←HL,paddedPast_full] at HE
 exact HE

include H h hk in
theorem rules_last_instantiated : (D).rules (pairFst key)=
    instantiate (IntegralMixedFramedFamilyRunView.stateView P D H key)
      (IntegralMixedSourceIntegerRecordAppend.step P S hn hd hcap N (pairFst key) oldCodes.length)::commands P D key:=by
 exact (rules_last P S hn hd hcap N T hz hT hroom key oldCodes code h hk).trans
   (congrArg (fun c=>c::commands P D key)
     (last_instruction P S hn hd hcap N T hz hT hroom H key oldCodes code h hk))

theorem parent_currentQ : commonDenominator (IntegralMixedFramedFamilyRunView.stateView P D H key)=
    commonDenominator (run (initial P D (pairFst key)) (commands P D key)
      (by rw [commands,paddedPast_length];exact (min_le_right _ _).trans (Nat.le_succ _))):=rfl

end LeanCanny.Encoding.IntegralMixedSourceIntegerLastCode
