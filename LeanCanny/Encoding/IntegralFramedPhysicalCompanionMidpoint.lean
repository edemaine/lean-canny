/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalCompanionPoint
public import LeanCanny.Geometry.IntegralMixedChronologicalMidpointCriticalReadback
/-! # An active midpoint record reads one actual mean-slice critical point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalCompanionPoint
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (commands prefixLength defaultInstruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (BK : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
  (hr : IntegralMixedFramedHeaderBits.Represents BK.parameters BK.plan BK.data T)
include hr
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "S"=>IntegralFramedPhysicalBankTerm.input BK
attribute [local irreducible] geometricPoint IntegralMixedFramedHistoryFamilyBits.family IntegralFramedPhysicalSquare.point

theorem midpoint_frame_point (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w)
    (b : ℕ) (hb : Active BK T c b) (labels : List Bool) (aIndex bIndex g j : ℕ)
    (HG : IntegralMixedChronologicalMidpointCode.Good ((P).ambient (pairFst ((BK).key c))) b labels aIndex bIndex g j)
    (hc : (IntegralMixedFramedRootPullback.instructionAt P (BK).plan (pairFst ((BK).key c)) b).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData ((P).ambient (pairFst ((BK).key c))) b labels aIndex bIndex g j HG).rule) :
    let Q:=(IntegralMixedFramedRootPullback.instructionAt P (BK).plan (pairFst ((BK).key c)) b).source
    let p:=geometricPoint BK T c w hv b
    let value:=(fun i (_hi : i<b)=>IntegralFramedPhysicalSquare.point P (BK).plan (BK).data
      (BK).nodes (BK).factor (BK).seed (BK).bounds (BK).key (BK).positive c w hv
      ⟨prefixLength P ((BK).key c)-1-i,by
        rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
        have HB:=(active_direct BK T c b hb).1
        omega⟩)
    (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
    (∀i (hi : i<WordListRecords.count labels),p ⟨i,hi.trans_le HG.1.1⟩=
      value (Nat.fromBitsLE (WordList.get labels i)) (HG.1.2 i hi)) ∧
    p ⟨WordListRecords.count labels,by have H1:=HG.2.2.2.1;have H2:=HG.2.2.2.2.1;omega⟩=
      (value aIndex HG.2.1+value bIndex HG.2.2.1)/2 ∧
    ∀ (i : Fin ((P).ambient (pairFst ((BK).key c))+1)), Nat.le (WordListRecords.count labels+1) (Fin.val i) → Ne (Fin.val i) g →
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂
        (Int.castRingHom ℝ) p=0 :=by
  let r:=(IntegralMixedChronologicalMidpointCode.rawData ((P).ambient (pairFst ((BK).key c))) b labels aIndex bIndex g j HG).rule
  let newer:=(commands P (BK).plan ((BK).key c)).take (IntegralMixedFramedCriticalGuardBits.age P (BK).key (fun _=>b) c)
  let older:=paddedPast (defaultInstruction P (BK).plan (pairFst ((BK).key c))) ((BK).plan.rules (pairFst ((BK).key c))) b
  obtain ⟨hcs,φ,Hφ,HP⟩:=exists_critical BK T hr c w hv b hb r hc
  let x:=IntegralFramedPhysicalCriticalReadback.oldState P (BK).plan (BK).data (BK).key c _ _ r newer older hcs
  have HM : older.length=b:=paddedPast_length _ _ _
  have HT : (commands P (BK).plan ((BK).key c)).length=prefixLength P ((BK).key c):=paddedPast_length _ _ _
  have HL : (commands P (BK).plan ((BK).key c)).length=newer.length+1+older.length:=by
    have HH:=congrArg List.length hcs
    simpa only [newer,older,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using HH
  let v : Fin older.length→ℝ:=fun i=>IntegralFramedPhysicalSquare.point P (BK).plan (BK).data
    (BK).nodes (BK).factor (BK).seed (BK).bounds (BK).key (BK).positive c w hv
    ⟨newer.length+1+i.val,by rw [IntegralMixedFramedHistoryFamilyBits.family_birth,←HT];omega⟩
  have HV : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=v i:=by
    intro i
    exact IntegralFramedPhysicalCriticalReadback.quotient_full P (BK).plan (BK).data (BK).nodes (BK).factor (BK).seed
      (BK).bounds (BK).key (BK).positive c w hv _ _ r newer older hcs φ Hφ i
  have HR:=IntegralMixedChronologicalMidpoint.raw_readback x
    (IntegralFramedPhysicalCriticalReadback.older_room P (BK).plan (BK).data (BK).key c _ _ r newer older hcs)
    b HM labels aIndex bIndex g j HG φ v HV (geometricPoint BK T c w hv b) HP
  have transport (i : ℕ) (hi : i<b) : v ⟨older.length-1-i,by omega⟩=
      IntegralFramedPhysicalSquare.point P (BK).plan (BK).data (BK).nodes (BK).factor (BK).seed (BK).bounds
        (BK).key (BK).positive c w hv
        ⟨prefixLength P ((BK).key c)-1-i,by rw [IntegralMixedFramedHistoryFamilyBits.family_birth];omega⟩ :=by
    unfold v
    congr 1
    apply Fin.ext
    change newer.length+1+(older.length-1-i)=prefixLength P ((BK).key c)-1-i
    omega
  refine ⟨HR.1,?_,?_,HR.2.2.2⟩
  · intro i hi
    exact (HR.2.1 i hi).trans (transport _ (HG.1.2 i hi))
  · exact HR.2.2.1.trans (congrArg₂ (fun u v : ℝ=>(u+v)/2) (transport aIndex HG.2.1) (transport bIndex HG.2.2.1))


theorem selected_of_midpoint (c : List Bool) (b : ℕ) (labels : List Bool) (aIndex bIndex g j : ℕ)
    (HG : IntegralMixedChronologicalMidpointCode.Good ((P).ambient (pairFst ((BK).key c))) b labels aIndex bIndex g j)
    (hc : (IntegralMixedFramedRootPullback.instructionAt P (BK).plan (pairFst ((BK).key c)) b).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData ((P).ambient (pairFst ((BK).key c))) b labels aIndex bIndex g j HG).rule) :
    selected BK T c b=j :=by
  unfold selected
  rw [IntegralFramedPhysicalCriticalReadback.header_packet P (BK).plan (BK).data
    T hr
    (BK).key IntegralFramedPhysicalCriticalGuardScan.stage c (List.replicate b true) b
    (by simp only [IntegralFramedPhysicalCriticalGuardScan.stage,pairSnd_pair,List.length_replicate])]
  rw [hc]
  exact IntegralMixedChronologicalMidpoint.raw_selected b labels aIndex bIndex g j HG

end LeanCanny.Encoding.IntegralFramedPhysicalCompanionPoint
