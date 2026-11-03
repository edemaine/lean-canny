/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedReservedCutCode
public import LeanCanny.Encoding.IntegralFramedPaddedCutVertex
/-! # A literal final typed raw cut produces one full word at the same root

Only an honest parent realization is assumed. The instruction-list head,
source, current-Q rule, kind and degree are derived from the raw code.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedReservedCutVertex
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
 (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
 (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
 (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
 (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
 (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
local notation "D"=>IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom
attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
variable (H : IntegralMixedFramedHistoryFamilyBits.Data P (IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom)) (key : List Bool) (oldCodes : List (List Bool))
 (d : IntegralMixedCutRecordConstructor.Data (P.ambient (pairFst key)) (N (pairFst key)+oldCodes.length))
 (tag : Tag) (choice degree : ℕ)
 (hdegree : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst key)+1)
   (S (pairFst key) (N (pairFst key)+oldCodes.length)).degree)
 (htable : IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode (oldCodes++[d.code tag choice degree]))
 (hk : prefixLength P key=N (pairFst key)+oldCodes.length)

include htable in
theorem child_positive : 0<(family P D H).birth
    (keyAt (pairFst key) ((D).rules (pairFst key)).length []):=by
 rw [family_birth,keyAt_prefix P _ _ [] (by have HB:=(D).room (pairFst key);omega),
   IntegralMixedSourceIntegerLastCode.rules_length_last P S hn hd hcap N T hz hT hroom _ oldCodes _ htable]
 omega

include hdegree htable hk in
theorem exists_vertex (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hmargin : IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst key)+1) (P.degree (pairFst key))<2^P.width (pairFst key))
    (v : ℕ→ℝ) (hv : IntegralMixedIntegerRealization.Realizes (IntegralMixedFramedFamilyRunView.stateView P D H key) v) :
    let terminal:=fun _ : List Bool=>keyAt (pairFst key) ((D).rules (pairFst key)).length []
    let hp:=fun _ : List Bool=>child_positive P S hn hd hcap N T hz hT hroom H key oldCodes d tag choice degree htable
    ∃w,∃hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hp) [] w,
      w.length=SquareSampleCompleteVertices.width (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hp) [] ∧
      ∀i : Fin ((family P D H).birth (terminal [])),
        IntegralFramedPhysicalSquare.point P D H L F C hs terminal hp [] w hw i=IntegralFramedPaddedCutVertex.values v i.val:=by
 dsimp only
 let Q:=S (pairFst key) (N (pairFst key)+oldCodes.length)
 have HA : IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst key)+1) Q.degree≤2^P.width (pairFst key):=by
   rw [hd]
   exact hcap _
 let cd:=d.cut Q tag choice degree hdegree HA
 let x:=IntegralMixedFramedFamilyRunView.stateView P D H key
 have HD : degree<2^P.width (pairFst key):=hdegree.trans_lt (by rw [hd];exact hmargin)
 have HE:=IntegralMixedReservedCutCode.rules_last_decoded P S hn hd hcap N T hz hT hroom H key oldCodes d tag choice degree hdegree htable hk
 change (D).rules (pairFst key)=⟨Q,
   (IntegralMixedCausalUnitRecordBits.record Q (hn _) (N (pairFst key)+oldCodes.length) (d.code tag choice degree) HA).source_cap,
   .cut (cd.rule (commonDenominator x) (commonDenominator_ne_zero x))
     (cd.kind (commonDenominator x) (commonDenominator_ne_zero x)) degree hdegree HD.le⟩::commands P D key at HE
 exact IntegralFramedPaddedCutVertex.exists_vertex P D H L F C hs (pairFst key) (commands P D key) Q
   (IntegralMixedCausalUnitRecordBits.record Q (hn _) (N (pairFst key)+oldCodes.length) (d.code tag choice degree) HA).source_cap
   (cd.rule (commonDenominator x) (commonDenominator_ne_zero x))
   (cd.kind (commonDenominator x) (commonDenominator_ne_zero x)) degree hdegree HD HE v hv

end LeanCanny.Encoding.IntegralMixedReservedCutVertex
