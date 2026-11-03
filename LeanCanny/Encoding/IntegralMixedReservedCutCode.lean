/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerLastCode
public import LeanCanny.Encoding.IntegralMixedCutRecordConstructor
/-! # A typed last virtual word decodes at the actual parent denominator -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedReservedCutCode
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits
open IntegralMixedCutRecordConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem template_decode {n B birth : ℕ} (d : IntegralMixedCutRecordConstructor.Data n birth) (Q : SpatialSource n) (hn : 0<n)
    (tag : Tag) (choice degree : ℕ) (hd : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B) :
    (IntegralMixedCausalUnitRecordBits.record Q hn birth (d.code tag choice degree) hcap).template=
      .cut (d.cut Q tag choice degree hd hcap):=by
 simp only [IntegralMixedCausalUnitRecordBits.record,IntegralMixedUnitRecordCode.critical,field_0,
   show ([] : List Bool)[0]?.getD false=false from rfl,Bool.false_eq_true,ite_false]
 rw [cut_decode d Q tag choice degree hd hcap]

noncomputable def instruction {n B birth S m : ℕ} {Q0 : SpatialSource n} {ι : Type}
    (x : State Q0 S B m ι) (d : IntegralMixedCutRecordConstructor.Data n birth) (Q : SpatialSource n) (hn : 0<n)
    (tag : Tag) (choice degree : ℕ) (hd : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B) : Instruction n B where
 source:=Q
 source_cap:=(IntegralMixedCausalUnitRecordBits.record Q hn birth (d.code tag choice degree) hcap).source_cap
 command:=.cut ((d.cut Q tag choice degree hd hcap).rule (commonDenominator x) (commonDenominator_ne_zero x))
   ((d.cut Q tag choice degree hd hcap).kind (commonDenominator x) (commonDenominator_ne_zero x)) degree hd (hd.trans hcap)

theorem instantiate_decode {n B birth S m : ℕ} {Q0 : SpatialSource n} {ι : Type}
    (x : State Q0 S B m ι) (d : IntegralMixedCutRecordConstructor.Data n birth) (Q : SpatialSource n) (hn : 0<n)
    (tag : Tag) (choice degree : ℕ) (hd : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B) :
    instantiate x (IntegralMixedCausalUnitRecordBits.record Q hn birth (d.code tag choice degree) hcap)=
      instruction x d Q hn tag choice degree hd hcap:=by
 unfold instantiate
 rw [template_decode d Q hn tag choice degree hd hcap]
 rfl

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
 (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
 (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
 (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
 (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
 (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
local notation "D"=>IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom
variable (H : IntegralMixedFramedHistoryFamilyBits.Data P (IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom)) (key : List Bool) (oldCodes : List (List Bool))
 (d : IntegralMixedCutRecordConstructor.Data (P.ambient (pairFst key)) (N (pairFst key)+oldCodes.length)) (tag : Tag) (choice degree : ℕ)
 (hdegree : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst key)+1)
   (S (pairFst key) (N (pairFst key)+oldCodes.length)).degree)
 (htable : IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode (oldCodes++[d.code tag choice degree]))
 (hk : prefixLength P key=N (pairFst key)+oldCodes.length)

include H htable hk in
theorem rules_last_decoded : (D).rules (pairFst key)=
    instruction (IntegralMixedFramedFamilyRunView.stateView P D H key) d (S (pairFst key) (N (pairFst key)+oldCodes.length))
      (hn _) tag choice degree hdegree (by rw [hd];exact hcap _)::commands P D key:=by
 rw [IntegralMixedSourceIntegerLastCode.rules_last_instantiated P S hn hd hcap N T hz hT hroom H key oldCodes
   (d.code tag choice degree) htable hk]
 apply congrArg (fun c=>c::commands P D key)
 unfold IntegralMixedSourceIntegerRecordAppend.step
 rw [IntegralMixedSourceIntegerLastCode.code_last _ oldCodes _ htable]
 exact instantiate_decode _ d _ (hn _) tag choice degree hdegree _

end LeanCanny.Encoding.IntegralMixedReservedCutCode
