/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
public import LeanCanny.Algebra.IntegralMixedStaticRecordPrefix
/-! # Decoded original bytes compile against the literal older causal bank -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalUnitContinuation
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedCausalRecordBits
open IntegralMixedFramedHistoryScript (Instruction)
open IntegralMixedCausalPlanBits (commands commands_cons commands_length)
open IntegralMixedFramedFixedContinuation (wrap)
open LeanCanny.Geometry.IntegralMixedOptionalEndpoints (Decodes)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]

omit [Fintype ι] in
noncomputable def records (Q :SpatialSource n) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B) (birth :ℕ) :
    List (List Bool)→List (Record n B)
  | []=>[]
  | code::codes=>IntegralMixedCausalUnitRecordBits.record Q hn (birth+codes.length) code hcap::records Q hn hcap birth codes

theorem records_length (Q :SpatialSource n) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B) (birth :ℕ) (codes :List (List Bool)) :
    (records Q hn hcap birth codes).length=codes.length:=by
  induction codes with
  | nil=>rfl
  | cons code codes ih=>simp only [records,List.length_cons,ih]

theorem records_reverse_get (Q :SpatialSource n) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B) (birth :ℕ)
    (codes :List (List Bool)) (i :ℕ) (hi :i<codes.length) :
    (records Q hn hcap birth codes).reverse[i]?=
      some (IntegralMixedCausalUnitRecordBits.record Q hn (birth+i) ((codes.reverse[i]?).getD []) hcap):=by
  induction codes generalizing i with
  | nil=>simp only [List.length_nil] at hi;omega
  | cons code codes ih=>
    simp only [records,List.reverse_cons]
    by_cases HI :i<codes.length
    · rw [List.getElem?_append_left (by rw [List.length_reverse,records_length];exact HI),ih i HI]
      rw [List.getElem?_append_left (by rw [List.length_reverse];exact HI)]
    · have HE :i=codes.length:=by simp only [List.length_cons] at hi;omega
      subst i
      have HL :(records Q hn hcap birth codes).reverse.length=codes.length:=by rw [List.length_reverse,records_length]
      rw [List.getElem?_append_right (show (records Q hn hcap birth codes).reverse.length≤codes.length by rw [HL]),
        HL,Nat.sub_self,List.getElem?_cons_zero]
      rw [List.getElem?_append_right (show codes.reverse.length≤codes.length by rw [List.length_reverse])]
      simp only [List.length_reverse,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]

theorem decode_length {m :ℕ} {Q :SpatialSource n} {κ :Type} [Fintype κ]
    (x :State Q S B m κ) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
    (cs :List (IntegralMixedFullHistoryScript.Command Q B)) (hc :m+cs.length≤S+1)
    (codes :List (List Bool)) (HD :Decodes x hn hcap cs hc codes) :codes.length=cs.length:=by
  induction cs generalizing codes with
  | nil=>have HE :codes=[]:=HD;rw [HE];rfl
  | cons c cs ih=>
    cases codes with
    | nil=>exact HD.elim
    | cons code codes=>exact congrArg (·+1) (ih _ codes HD.1)

theorem reframe_run_congr (initial :State P S B 0 ι)
    (cs ds :List (Instruction n B)) (hc :cs.length≤S+1) (hd :ds.length≤S+1) (HE :cs=ds)
    (Q :SpatialSource n) (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) :
    HEq (reframe (IntegralMixedFramedHistoryScript.run initial cs hc) Q hQ)
      (reframe (IntegralMixedFramedHistoryScript.run initial ds hd) Q hQ):=by cases HE;rfl

theorem commands_congr (initial :State P S B 0 ι)
    (rs ds :List (Record n B)) (hr :rs.length≤S+1) (hd :ds.length≤S+1) (HE :rs=ds) :
    commands initial rs hr=commands initial ds hd:=by cases HE;rfl

variable (initial :State P S B 0 ι) (Q :SpatialSource n) (hn :0<n)
  (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
  (older :List (Record n B)) (ho :older.length≤S+1)
local notation "hQ"=>IntegralMixedStaticRecordPrefix.cap Q hcap
local notation "old"=>commands initial older ho

noncomputable def start :=reframe (IntegralMixedFramedHistoryScript.run initial old
  (by rw [commands_length];exact ho)) Q hQ

theorem compile_commands (cs :List (IntegralMixedFullHistoryScript.Command Q B))
    (hc :(old).length+cs.length≤S+1) (codes :List (List Bool))
    (HD :Decodes (start initial Q hcap older ho) hn hcap cs hc codes) :
    commands initial (records Q hn hcap (old).length codes++older)
      (by
        rw [List.length_append,records_length]
        have HL:=decode_length (start initial Q hcap older ho) hn hcap cs hc codes HD
        have HO:=commands_length initial older ho
        omega)=cs.map (wrap Q hQ)++old :=by
  induction cs generalizing codes with
  | nil=>
    have HE :codes=[]:=HD
    subst codes
    rfl
  | cons c cs ih=>
    cases codes with
    | nil=>exact HD.elim
    | cons code codes=>
      have HT :(old).length+cs.length≤S+1:=by simp only [List.length_cons] at hc;omega
      have HL:=decode_length (start initial Q hcap older ho) hn hcap cs HT codes HD.1
      have IH:=ih (hc:=HT) (codes:=codes) HD.1
      let rs:=records Q hn hcap (old).length codes++older
      have HR :rs.length≤S+1:=by
        simp only [rs,List.length_append,records_length]
        have HO:=commands_length initial older ho
        omega
      let tail:=commands initial rs HR
      have Htail :tail=cs.map (wrap Q hQ)++old:=IH
      let y:=IntegralMixedFramedHistoryScript.run initial tail (by rw [commands_length];exact HR)
      have Hstate:= (reframe_run_congr initial tail (cs.map (wrap Q hQ)++old)
        (by rw [commands_length];exact HR) (by simp only [List.length_append,List.length_map];omega) Htail Q hQ).trans
        (IntegralMixedFramedFixedContinuation.run_append initial Q hQ old
          (by rw [commands_length];exact ho) cs HT)
      have HM :tail.length=(old).length+cs.length:=by rw [Htail,List.length_append,List.length_map];omega
      have HI :IntegralMixedFramedHistoryScript.Index ι tail=
          IntegralMixedFullHistoryScript.Index (IntegralMixedFramedHistoryScript.Index ι old) cs:=
        (congrArg (IntegralMixedFramedHistoryScript.Index ι) Htail).trans
          (IntegralMixedFramedFixedContinuation.index_append Q hQ cs old)
      have HQ:=LeanCanny.Geometry.IntegralMixedOptionalEndpoints.commonDenominator_heq
        (reframe y Q hQ)
        (IntegralMixedFullHistoryScript.continueRun (start initial Q hcap older ho) cs HT) HM HI Hstate
      have HC:=LeanCanny.Geometry.IntegralMixedOptionalEndpoints.decoded_command_congr hn
        ((old).length+codes.length) ((old).length+cs.length) code hcap
        (commonDenominator y) (commonDenominator (IntegralMixedFullHistoryScript.continueRun
          (start initial Q hcap older ho) cs HT)) (commonDenominator_ne_zero y) (commonDenominator_ne_zero _)
        (congrArg ((old).length+·) HL) HQ
      have HDc :(IntegralMixedCausalUnitRecordBits.record Q hn ((old).length+codes.length) code hcap).template.command
          (commonDenominator y) (commonDenominator_ne_zero y)=c:=HC.trans HD.2
      have HE :instantiate y (IntegralMixedCausalUnitRecordBits.record Q hn ((old).length+codes.length) code hcap)=wrap Q hQ c:=by
        unfold instantiate wrap
        rw [HDc]
        rfl
      change commands initial
        (IntegralMixedCausalUnitRecordBits.record Q hn ((old).length+codes.length) code hcap::rs) _ =_
      rw [commands_cons]
      change instantiate y (IntegralMixedCausalUnitRecordBits.record Q hn ((old).length+codes.length) code hcap)::tail=
        wrap Q hQ c::(cs.map (wrap Q hQ)++old)
      rw [HE,Htail]

theorem compile_run (cs :List (IntegralMixedFullHistoryScript.Command Q B))
    (hc :(old).length+cs.length≤S+1) (codes :List (List Bool))
    (HD :Decodes (start initial Q hcap older ho) hn hcap cs hc codes) :
    HEq (reframe (IntegralMixedFramedHistoryScript.run initial
      (commands initial (records Q hn hcap (old).length codes++older) (by
        rw [List.length_append,records_length]
        have HL:=decode_length (start initial Q hcap older ho) hn hcap cs hc codes HD
        have HO:=commands_length initial older ho
        omega)) (by
        rw [commands_length,List.length_append,records_length]
        have HL:=decode_length (start initial Q hcap older ho) hn hcap cs hc codes HD
        have HO:=commands_length initial older ho
        omega)) Q hQ)
      (IntegralMixedFullHistoryScript.continueRun (start initial Q hcap older ho) cs hc):=by
  exact (reframe_run_congr initial _ _ _ _ (compile_commands initial Q hn hcap older ho cs hc codes HD) Q hQ).trans
    (IntegralMixedFramedFixedContinuation.run_append initial Q hQ old (by rw [commands_length];exact ho) cs hc)

theorem compile_index (cs :List (IntegralMixedFullHistoryScript.Command Q B))
    (hc :(old).length+cs.length≤S+1) (codes :List (List Bool))
    (HD :Decodes (start initial Q hcap older ho) hn hcap cs hc codes) :
    IntegralMixedFramedHistoryScript.Index ι (commands initial (records Q hn hcap (old).length codes++older) (by
        rw [List.length_append,records_length]
        have HL:=decode_length (start initial Q hcap older ho) hn hcap cs hc codes HD
        have HO:=commands_length initial older ho
        omega))=
      IntegralMixedFullHistoryScript.Index (IntegralMixedFramedHistoryScript.Index ι old) cs:=
  (congrArg (IntegralMixedFramedHistoryScript.Index ι) (compile_commands initial Q hn hcap older ho cs hc codes HD)).trans
    (IntegralMixedFramedFixedContinuation.index_append Q hQ cs old)

end LeanCanny.Algebra.IntegralMixedCausalUnitContinuation
