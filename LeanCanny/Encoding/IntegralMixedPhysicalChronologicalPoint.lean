/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalGeometry
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalValues
public import LeanCanny.Geometry.IntegralMixedChronologicalCriticalReadback
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualitySemantics
/-! # A checked chronological critical record reads an actual frozen point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionScan
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedPhysicalMarkedPlan (bank tables represents)
open IntegralMixedFramedHistoryFamilyBits (commands prefixLength defaultInstruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R :List Bool→ℕ} (hR :BinaryFn R) (outer :Bool)
local notation "B"=>bank hn ht ha hR outer
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "T"=>tables hn ht ha hR outer
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer
attribute [local irreducible] bank tables geometricPoint
  IntegralMixedFramedHistoryFamilyBits.family IntegralFramedPhysicalSquare.point

theorem frame_point (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w)
    (b :ℕ) (hb :Active hn ht ha hR outer c b) (labels :List Bool) (g j :ℕ)
    (HG :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (pairFst ((B).key c))) b labels g j)
    (hc :(IntegralMixedFramedRootPullback.instructionAt P (B).plan (pairFst ((B).key c)) b).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient (pairFst ((B).key c))) b labels g j HG).rule) :
    let Q:=(IntegralMixedFramedRootPullback.instructionAt P (B).plan (pairFst ((B).key c)) b).source
    let p:=geometricPoint hn ht ha hR outer c w hv b
    (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
    (∀i (hi :i<WordListRecords.count labels),p ⟨i,hi.trans_le HG.1.1⟩=
      IntegralFramedPhysicalSquare.point P (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (full_positive hn ht ha hR outer) c w hv
        ⟨prefixLength P ((B).key c)-1-Nat.fromBitsLE (WordList.get labels i),by
          rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
          have HB:=(active_direct hn ht ha hR outer c b hb).1
          omega⟩) ∧
    ∀ (i :Fin ((P).ambient (pairFst ((B).key c))+1)), (WordListRecords.count labels ≤ i.val) → i.val≠g →
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂
        (Int.castRingHom ℝ) p=0 :=by
  let r:=(IntegralMixedChronologicalFrameCode.rawData ((P).ambient (pairFst ((B).key c))) b labels g j HG).rule
  let newer:=(commands P (B).plan ((B).key c)).take (IntegralMixedFramedCriticalGuardBits.age P (B).key (fun _=>b) c)
  let older:=paddedPast (defaultInstruction P (B).plan (pairFst ((B).key c))) ((B).plan.rules (pairFst ((B).key c))) b
  obtain ⟨hcs,φ,Hφ,HP⟩:=exists_critical hn ht ha hR outer c w hv b hb r hc
  let x:=IntegralFramedPhysicalCriticalReadback.oldState P (B).plan (B).data (B).key c _ _ r newer older hcs
  have HM :older.length=b:=paddedPast_length _ _ _
  have HT :(commands P (B).plan ((B).key c)).length=prefixLength P ((B).key c):=paddedPast_length _ _ _
  have HL :(commands P (B).plan ((B).key c)).length=newer.length+1+older.length:=by
    have HH:=congrArg List.length hcs
    simpa only [newer,older,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using HH
  let v :Fin older.length→ℝ:=fun i=>IntegralFramedPhysicalSquare.point P (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (B).key (full_positive hn ht ha hR outer) c w hv
    ⟨newer.length+1+i.val,by rw [IntegralMixedFramedHistoryFamilyBits.family_birth,←HT];omega⟩
  have HV :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=v i:=by
    intro i
    exact IntegralFramedPhysicalCriticalReadback.quotient_full P (B).plan (B).data (B).nodes (B).factor (B).seed
      (B).bounds (B).key (full_positive hn ht ha hR outer) c w hv _ _ r newer older hcs φ Hφ i
  have HR:=IntegralMixedChronologicalFrame.raw_readback x
    (IntegralFramedPhysicalCriticalReadback.older_room P (B).plan (B).data (B).key c _ _ r newer older hcs)
    b HM labels g j HG φ v HV (geometricPoint hn ht ha hR outer c w hv b) HP
  refine ⟨HR.1,?_,HR.2.2⟩
  intro i hi
  refine (HR.2.1 i hi).trans ?_
  unfold v
  congr 1
  apply Fin.ext
  change newer.length+1+(older.length-1-Nat.fromBitsLE (WordList.get labels i))=
    prefixLength P ((B).key c)-1-Nat.fromBitsLE (WordList.get labels i)
  have HH:=HG.1.2 i hi
  omega

theorem selected_of_frame (c :List Bool) (b :ℕ) (labels :List Bool) (g j :ℕ)
    (HG :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (pairFst ((B).key c))) b labels g j)
    (hc :(IntegralMixedFramedRootPullback.instructionAt P (B).plan (pairFst ((B).key c)) b).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient (pairFst ((B).key c))) b labels g j HG).rule) :
    selected hn ht ha hR outer c b=j :=by
  unfold selected
  rw [IntegralFramedPhysicalCriticalReadback.header_packet P (B).plan (B).data T (represents hn ht ha hR outer)
    (B).key IntegralFramedPhysicalCriticalGuardScan.stage c (List.replicate b true) b
    (by simp only [IntegralFramedPhysicalCriticalGuardScan.stage,pairSnd_pair,List.length_replicate])]
  rw [hc]
  exact IntegralMixedChronologicalFrame.raw_selected b labels g j HG

end LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionScan

namespace LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R :List Bool→ℕ} (hR :BinaryFn R)
local notation "B"=>bank hn ht ha hR false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha hR false
attribute [local irreducible] bank IntegralMixedFramedHistoryFamilyBits.family IntegralFramedPhysicalSquare.point

theorem point_full (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w) (label :ℕ)
    (hl :label<IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key c)) :
    point hn ht ha hR c w hv label=
      IntegralFramedPhysicalSquare.point P (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (IntegralMixedPhysicalPointCompanionScan.full_positive hn ht ha hR false) c w hv
        ⟨IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key c)-1-label,by
          rw [IntegralMixedFramedHistoryFamilyBits.family_birth];omega⟩ :=by
  have HC :count hn ht ha hR c=IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key c):=
    IntegralMixedFramedHistoryFamilyBits.family_birth P (B).plan (B).data ((B).key c)
  unfold point pointNewest
  apply congrArg (IntegralFramedPhysicalSquare.point P (B).plan (B).data (B).nodes (B).factor (B).seed
    (B).bounds (B).key (IntegralMixedPhysicalPointCompanionScan.full_positive hn ht ha hR false) c w hv)
  apply Fin.ext
  change min (newest (count hn ht ha hR c) label) (count hn ht ha hR c-1)=_
  rw [HC]
  unfold newest
  rw [min_eq_left (by omega :label≤IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key c)-1)]
  exact min_eq_left (Nat.sub_le _ _)

attribute [local semireducible] IntegralMixedFramedHistoryFamilyBits.family

theorem retained_point (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w)
    (b :ℕ) (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha hR false c b) :
    IntegralMixedPhysicalPointCompanionScan.retained hn ht ha hR false c w hv b hb=point hn ht ha hR c w hv b:=by
  have HB:=(IntegralMixedPhysicalPointCompanionScan.active_direct hn ht ha hR false c b hb).1
  rw [point_full hn ht ha hR c w hv b HB]
  unfold IntegralMixedPhysicalPointCompanionScan.retained LeanCanny.Geometry.IntegralMixedFramedCriticalGuard.actualPoint
    IntegralFramedPhysicalSquare.point LeanCanny.Geometry.IntegralMixedFramedCriticalGuard.fullEquiv
    IntegralMixedPhysicalPointCompanionScan.fullTuple IntegralFramedPhysicalCriticalGuardScan.point
    IntegralFramedPhysicalSquare.joint
  simp only [FixedWidthSuffixLiftBits.shift,Nat.zero_add,Fin.cast]
  exact IntegralFramedPhysicalCriticalReadback.indexedPoint_key_cast
    (IntegralMixedFramedHistoryFamilyBits.family P (B).plan (B).data)
    (fun k=>IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryFamilyBits.commands P (B).plan k))
    (fun k=>IntegralMixedFramedPhysicalIndex.enumerate (IntegralMixedFramedHistoryFamilyBits.commands P (B).plan k))
    _ _ (congrArg (B).key (pairFst_pair c (List.replicate b true))) _
    (IntegralMixedFramedCriticalGuardBits.count_actual P (B).plan (B).data
      (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false) (IntegralMixedPhysicalMarkedPlan.represents hn ht ha hR false) _ _)
    (IntegralMixedPhysicalGuardScan.count_eq hn ht ha hR false c (List.replicate b true)) _ _ _ (by
      change IntegralMixedFramedCriticalGuardBits.age P (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key)
        IntegralFramedPhysicalCriticalGuardScan.stage (pair c (List.replicate b true))=
        IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key c)-1-b
      simp only [IntegralMixedFramedCriticalGuardBits.age,IntegralFramedPhysicalCriticalGuardTest.keyDatum,
        IntegralFramedPhysicalCriticalGuardScan.stage,pairFst_pair,pairSnd_pair,List.length_replicate])

end LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
