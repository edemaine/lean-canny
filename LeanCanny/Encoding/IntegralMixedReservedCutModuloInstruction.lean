/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCutRecordModuloDegree
public import LeanCanny.Encoding.IntegralMixedSourceIntegerLastCode
public import LeanCanny.Algebra.IntegralMixedSelectedBadMembership
/-! # The actual last instruction has its literal modulo-degree cut ruling -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedReservedCutModuloInstruction
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def OrdinaryInstruction {n B : ℕ} (i : Instruction n B) : Prop:=
 match i.command with
 | .cut r k _ _ _=>IntegralMixedSelectedBadMembership.Ordinary r k
 | _=>False

def ruling {n B : ℕ} (i : Instruction n B) : Option (IntegralMixedCriticalSweep.Rule n):=
 match i.command with
 | .cut r _ _ _ _=>some r
 | _=>none

private noncomputable def selectionFor {n B : ℕ} {Q : SpatialSource n}
    (command : IntegralMixedFullHistoryScript.Command Q B)
    (fallback : IntegralMixedFullHistoryFamilyBits.Selection Q) : IntegralMixedFullHistoryFamilyBits.Selection Q:=
 match command with
 | .cut r k d ha _=>⟨r,k,d,ha⟩
 | _=>fallback

private theorem ordinary_selection {n B : ℕ} (i : Instruction n B)
    (fallback : IntegralMixedFullHistoryFamilyBits.Selection i.source) (ho : OrdinaryInstruction i) :
    IntegralMixedSelectedBadMembership.Ordinary (selectionFor i.command fallback).rule (selectionFor i.command fallback).kind:=by
 cases i with
 | mk Q hcap command=>
   cases command with
   | integer p hp hd=>exact False.elim ho
   | critical r=>exact False.elim ho
   | cut r k d ha hd=>exact ho

private theorem rule_selection {n B : ℕ} (i : Instruction n B)
    (fallback : IntegralMixedFullHistoryFamilyBits.Selection i.source) (r : IntegralMixedCriticalSweep.Rule n)
    (hr : ruling i=some r) : (selectionFor i.command fallback).rule=r:=by
 cases i with
 | mk Q hcap command=>
   cases command with
   | integer p hp hd=>cases hr
   | critical r'=>cases hr
   | cut r' k d ha hd=>exact Option.some.inj hr

private theorem selection_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) :selection P D H key=selectionFor (instruction P D key).command (H.fallback key):=by
 unfold selection selectionFor
 cases hc:(instruction P D key).command <;>rfl

theorem selected_ordinary (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (ho : OrdinaryInstruction (instruction P D key)) :
    IntegralMixedSelectedBadMembership.Ordinary ((family P D H).rule key) ((family P D H).kind key):=by
 change IntegralMixedSelectedBadMembership.Ordinary (selection P D H key).rule (selection P D H key).kind
 exact (congrArg (fun s : IntegralMixedFullHistoryFamilyBits.Selection (instruction P D key).source=>
   IntegralMixedSelectedBadMembership.Ordinary s.rule s.kind) (selection_eq P D H key)).mpr
     (ordinary_selection (instruction P D key) (H.fallback key) ho)

theorem selected_rule (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (r : IntegralMixedCriticalSweep.Rule (P.ambient (pairFst key)))
    (hr : ruling (instruction P D key)=some r) : (family P D H).rule key=r:=by
 change (selection P D H key).rule=r
 exact (congrArg (fun s : IntegralMixedFullHistoryFamilyBits.Selection (instruction P D key).source=>s.rule)
   (selection_eq P D H key)).trans (rule_selection (instruction P D key) (H.fallback key) r hr)

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
 (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
 (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
 (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
 (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
 (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
local notation "D"=>IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom
attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
variable (H : IntegralMixedFramedHistoryFamilyBits.Data P
 (IntegralMixedSourceIntegerRecordAppend.plan P S hn hd hcap N T hz hT hroom))
 (key : List Bool) (codes : List (List Bool))
 (d : IntegralMixedCutRecordConstructor.Data (P.ambient (pairFst key)) (N (pairFst key)+codes.length))
 (tag : Tag) (choice rawDegree : ℕ)
 (htable : IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode (codes++[d.code tag choice rawDegree]))
 (hk : prefixLength P key=N (pairFst key)+codes.length)

noncomputable def born :Instruction (P.ambient (pairFst key)) (P.width (pairFst key)):=
 let Q:=S (pairFst key) (N (pairFst key)+codes.length)
 let hc :IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst key)+1) Q.degree≤2^P.width (pairFst key):=by
   rw [hd];exact hcap _
 let x:=IntegralMixedFramedFamilyRunView.stateView P D H key
 ⟨Q,(IntegralMixedCausalUnitRecordBits.record Q (hn _) (N (pairFst key)+codes.length) (d.code tag choice rawDegree) hc).source_cap,
   .cut (d.rule (commonDenominator x) (commonDenominator_ne_zero x))
     ((d.cut Q tag choice (IntegralMixedCutRecordConstructor.degreeResidue Q rawDegree)
       (IntegralMixedCutRecordConstructor.degreeResidue_le Q rawDegree) hc).kind
         (commonDenominator x) (commonDenominator_ne_zero x))
     (IntegralMixedCutRecordConstructor.degreeResidue Q rawDegree)
     (IntegralMixedCutRecordConstructor.degreeResidue_le Q rawDegree)
     ((IntegralMixedCutRecordConstructor.degreeResidue_le Q rawDegree).trans hc)⟩

include htable hk in
theorem instruction_eq :instruction P D key=born P S hn hd hcap N T hz hT hroom H key codes d tag choice rawDegree:=by
 rw [IntegralMixedSourceIntegerLastCode.last_instruction P S hn hd hcap N T hz hT hroom H key codes
   (d.code tag choice rawDegree) htable hk]
 unfold IntegralMixedSourceIntegerRecordAppend.step
 rw [IntegralMixedSourceIntegerLastCode.code_last _ codes _ htable]
 unfold instantiate born
 congr 1
 exact IntegralMixedCutRecordConstructor.command_decode_mod d _ (hn _) tag choice rawDegree _ _ _

theorem born_ordinary
    (ho : IntegralMixedCutRecordConstructor.tagIndex tag<3) :
    OrdinaryInstruction (born P S hn hd hcap N T hz hT hroom H key codes d tag choice rawDegree):=by
 cases tag with
 | coordinate=>change (0:ℕ)<3;decide
 | squarefree=>change (1:ℕ)<3;decide
 | value=>change (2:ℕ)<3;decide
 | limitCoordinate=>exact False.elim (Nat.lt_irrefl 3 ho)

include H htable hk in
theorem ordinary_at_parent
    (ho : IntegralMixedCutRecordConstructor.tagIndex tag<3) :OrdinaryInstruction (instruction P D key):=by
 rw [instruction_eq P S hn hd hcap N T hz hT hroom H key codes d tag choice rawDegree htable hk]
 exact born_ordinary P S hn hd hcap N T hz hT hroom H key codes d tag choice rawDegree ho

include htable hk in
theorem rule_at_parent : (family P D H).rule key=
    d.rule (commonDenominator (IntegralMixedFramedFamilyRunView.stateView P D H key))
      (commonDenominator_ne_zero (IntegralMixedFramedFamilyRunView.stateView P D H key)):=by
 apply selected_rule
 exact (congrArg ruling (instruction_eq P S hn hd hcap N T hz hT hroom H key codes d tag choice rawDegree htable hk)).trans rfl

end LeanCanny.Encoding.IntegralMixedReservedCutModuloInstruction
