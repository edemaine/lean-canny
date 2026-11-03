/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedReservedCutVertex
public import LeanCanny.Encoding.IntegralFramedPhysicalRealizedVertex
/-! # Typed reserved cuts produce a fresh word in the actual native sampler

The literal full key is supplied by structural root/count equalities. The
padded real root is sampled afresh there; no old or constant-context ordinal
is relabelled into another input family.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedReservedCutActualVertex
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits IntegralMixedIntegerRealization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem realizes_list_iff {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) (v : ℕ→ℝ) :
    Realizes (run x cs hc) v↔Realizes (run x ds hd) v:=by cases he;rfl

theorem vertex_from_full_run (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hp : ∀c,0<(family P D H).birth (key c)) (c root : List Bool)
    (hr : pairFst (key c)=root) (hc : prefixLength P (key c)=(D.rules root).length)
    (v : ℕ→ℝ)
    (hv : Realizes (run (initial P D root) (D.rules root) (by have H:=D.room root;omega)) v) :
    ∃w,∃hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w,
      w.length=SquareSampleCompleteVertices.width (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c ∧
      ∀i : Fin ((family P D H).birth (key c)),IntegralFramedPhysicalSquare.point P D H L F C hs key hp c w hw i=v i.val :=by
  cases hr
  have HE : commands P D (key c)=D.rules (pairFst (key c)):=by
    unfold commands
    rw [hc,paddedPast_full]
  have HV : Realizes ((family P D H).state (key c)) v:=by
    change Realizes (run (initial P D (pairFst (key c))) (commands P D (key c)) _) v
    exact (realizes_list_iff _ _ _ _ _ HE v).mpr hv
  exact IntegralFramedPhysicalSquare.exists_realized P D H L F C hs key hp c v HV

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
 (parent : List Bool) (codes : List (List Bool))
 (d : IntegralMixedCutRecordConstructor.Data (P.ambient (pairFst parent)) (N (pairFst parent)+codes.length))
 (tag : Tag) (choice degree : ℕ)
 (hdegree : degree≤IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst parent)+1)
   (S (pairFst parent) (N (pairFst parent)+codes.length)).degree)
 (htable : IntegralMixedCausalRecordPlanBits.records (pairFst parent)=WordList.encode (codes++[d.code tag choice degree]))
 (hk : prefixLength P parent=N (pairFst parent)+codes.length)

include hdegree htable hk in
theorem run_realizes
    (hmargin : IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst parent)+1) (P.degree (pairFst parent))<2^P.width (pairFst parent))
    (v : ℕ→ℝ) (hv : Realizes (IntegralMixedFramedFamilyRunView.stateView P D H parent) v) :
    Realizes (run (initial P D (pairFst parent)) ((D).rules (pairFst parent))
      (by have H:=(D).room (pairFst parent);omega)) (IntegralFramedPaddedCutVertex.values v):=by
  let Q:=S (pairFst parent) (N (pairFst parent)+codes.length)
  have HA : IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst parent)+1) Q.degree≤2^P.width (pairFst parent):=by
    rw [hd]
    exact hcap _
  let cd:=d.cut Q tag choice degree hdegree HA
  let x:=IntegralMixedFramedFamilyRunView.stateView P D H parent
  have HD : degree<2^P.width (pairFst parent):=hdegree.trans_lt (by rw [hd];exact hmargin)
  have HE:=IntegralMixedReservedCutCode.rules_last_decoded P S hn hd hcap N T hz hT hroom H parent codes d tag choice degree hdegree htable hk
  let born : Instruction (P.ambient (pairFst parent)) (P.width (pairFst parent)):=⟨Q,
    (IntegralMixedCausalUnitRecordBits.record Q (hn _) (N (pairFst parent)+codes.length) (d.code tag choice degree) HA).source_cap,
    .cut (cd.rule (commonDenominator x) (commonDenominator_ne_zero x))
      (cd.kind (commonDenominator x) (commonDenominator_ne_zero x)) degree hdegree HD.le⟩
  change (D).rules (pairFst parent)=born::commands P D parent at HE
  have HB : (born::commands P D parent).length≤(P.cap (pairFst parent)+1)+1:=by
    rw [←HE]
    have H:=(D).room (pairFst parent)
    omega
  have HV:=IntegralFramedPaddedCutVertex.run_realizes (initial P D (pairFst parent)) (commands P D parent)
    Q born.source_cap (cd.rule (commonDenominator x) (commonDenominator_ne_zero x))
    (cd.kind (commonDenominator x) (commonDenominator_ne_zero x)) degree hdegree HD HB v hv
  exact (realizes_list_iff _ _ _ _ HB HE _).mpr HV

include hdegree htable hk in
theorem exists_vertex (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hmargin : IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst parent)+1) (P.degree (pairFst parent))<2^P.width (pairFst parent))
    (key : List Bool→List Bool) (hp : ∀c,0<(family P D H).birth (key c)) (c : List Bool)
    (hr : pairFst (key c)=pairFst parent) (hc : prefixLength P (key c)=((D).rules (pairFst parent)).length)
    (v : ℕ→ℝ) (hv : Realizes (IntegralMixedFramedFamilyRunView.stateView P D H parent) v) :
    ∃w,∃hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w,
      w.length=SquareSampleCompleteVertices.width (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c ∧
      ∀i : Fin ((family P D H).birth (key c)),IntegralFramedPhysicalSquare.point P D H L F C hs key hp c w hw i=
        IntegralFramedPaddedCutVertex.values v i.val :=by
  exact vertex_from_full_run P D H L F C hs key hp c (pairFst parent) hr hc _
    (run_realizes P S hn hd hcap N T hz hT hroom H parent codes d tag choice degree hdegree htable hk hmargin v hv)

end LeanCanny.Encoding.IntegralMixedReservedCutActualVertex
