/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalCompanionPoint
public import LeanCanny.Encoding.IntegralFramedPhysicalBankChronologicalPoint
public import LeanCanny.Encoding.IntegralMixedPhysicalPointEquality
/-! # Same-word companion equalities and chronological bank quotients -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalCompanionPoint
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralFramedPhysicalCriticalGuardTest (keyDatum)
open IntegralMixedPhysicalPointEquality (left right coordinate context datum)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
  (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
include hr
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "S" => IntegralFramedPhysicalBankTerm.input B
local notation "HC" => count_eq B T hr
local notation "stage" => IntegralFramedPhysicalCriticalGuardScan.stage

noncomputable def PointAdmissible (q : List Bool) := IntegralMixedFramedPointEqualityBits.Admissible P T
  (keyDatum B.key) left right coordinate (context q)
noncomputable def pointValue := IntegralFramedPhysicalPointEqualityTest.value S P T B.key left right coordinate HC

theorem pointValue_zero_iff_block (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (a b i : ℕ)
    (h : PointAdmissible B T (pair (pair c w) (datum a b i))) :
    pointValue B T hr (pair (pair c w) (datum a b i))=InfinitesimalSign.encode 0 ↔
      block B T c w hv a i=block B T c w hv b i :=by
  have h':=h
  simp only [PointAdmissible,context,pairFst_pair,pairSnd_pair] at h'
  have HE:=IntegralFramedPhysicalPointEqualityTest.zero_iff S P T (B).key left right coordinate HC c w
    (datum a b i) hv h'
  have HL:=IntegralMixedFramedPointEqualityBits.column_lt P T (keyDatum (B).key) coordinate left
    (pair c (datum a b i)) h'.1 h'.2.2
  have HR:=IntegralMixedFramedPointEqualityBits.column_lt P T (keyDatum (B).key) coordinate right
    (pair c (datum a b i)) h'.2.1 h'.2.2
  have HN:=HC c (datum a b i)
  have HL' : IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate a true))+i<(S).count c :=by
    simpa only [IntegralMixedFramedPointEqualityBits.column,IntegralMixedFramedCriticalGuardBits.packet,
      keyDatum,left,coordinate,datum,pairFst_pair,pairSnd_pair,List.length_replicate,BinaryNatCode.encode,
      Nat.fromBitsLE_bits] using HL.trans_eq HN
  have HR' : IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate b true))+i<(S).count c :=by
    simpa only [IntegralMixedFramedPointEqualityBits.column,IntegralMixedFramedCriticalGuardBits.packet,
      keyDatum,right,coordinate,datum,pairFst_pair,pairSnd_pair,List.length_replicate,BinaryNatCode.encode,
      Nat.fromBitsLE_bits] using HR.trans_eq HN
  simpa only [pointValue,IntegralMixedFramedPointEqualityBits.point,IntegralFramedPhysicalPointEqualityTest.tuple,
    block,left,right,coordinate,datum,IntegralMixedFramedCriticalGuardBits.packet,keyDatum,
    pairFst_pair,pairSnd_pair,List.length_replicate,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    dite_eq_left HL',dite_eq_left HR',Fin.cast,IntegralMixedFramedCriticalGuardBits.physicalPower] using HE

theorem retained_env (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w)
    (b :ℕ) (hb :Active B T c b) :
    retained B T hr c w hv b hb=IntegralFramedPhysicalBankTerm.env B T hr c w hv b:=by
  have HB:=(active_direct B T c b hb).1
  rw [IntegralFramedPhysicalBankTerm.env_chronological B T hr c w hv b (by
    change b<(IntegralMixedFramedHistoryFamilyBits.family P B.plan B.data).birth (B.key c)
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    exact HB)]
  unfold retained LeanCanny.Geometry.IntegralMixedFramedCriticalGuard.actualPoint
    IntegralFramedPhysicalSquare.point LeanCanny.Geometry.IntegralMixedFramedCriticalGuard.fullEquiv
    fullTuple IntegralFramedPhysicalCriticalGuardScan.point
    IntegralFramedPhysicalSquare.joint
  simp only [FixedWidthSuffixLiftBits.shift,Nat.zero_add,Fin.cast]
  exact IntegralFramedPhysicalCriticalReadback.indexedPoint_key_cast
    (IntegralMixedFramedHistoryFamilyBits.family P (B).plan (B).data)
    (fun k=>IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryFamilyBits.commands P (B).plan k))
    (fun k=>IntegralMixedFramedPhysicalIndex.enumerate (IntegralMixedFramedHistoryFamilyBits.commands P (B).plan k))
    _ _ (congrArg (B).key (pairFst_pair c (List.replicate b true))) _
    (IntegralMixedFramedCriticalGuardBits.count_actual P (B).plan (B).data
      T hr _ _)
    (count_eq B T hr c (List.replicate b true)) _ _ _ (by
      change IntegralMixedFramedCriticalGuardBits.age P (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key)
        IntegralFramedPhysicalCriticalGuardScan.stage (pair c (List.replicate b true))=
        (IntegralMixedFramedHistoryFamilyBits.family P B.plan B.data).birth (B.key c)-1-b
      rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
      simp only [IntegralMixedFramedCriticalGuardBits.age,IntegralFramedPhysicalCriticalGuardTest.keyDatum,
        IntegralFramedPhysicalCriticalGuardScan.stage,pairFst_pair,pairSnd_pair,List.length_replicate])

omit hr in
theorem admissible_packet_iff (c w : List Bool) (a b i : ℕ) :
    PointAdmissible B T (pair (pair c w) (datum a b i)) ↔
    Active B T c a ∧ Active B T c b ∧ i<(P).ambient (pairFst (B.key c))+1 := by
  simp only [PointAdmissible,IntegralMixedFramedPointEqualityBits.Admissible,context,left,right,coordinate,
    datum,Active,IntegralMixedFramedCriticalGuardBits.Active,IntegralMixedFramedCriticalGuardBits.header,
    IntegralFramedPhysicalCriticalGuardScan.stage,keyDatum,pairFst_pair,pairSnd_pair,List.length_replicate,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem frame_point_env (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w)
    (b : ℕ) (hb : Active B T c b) (labels : List Bool) (g j : ℕ)
    (HG : IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (pairFst (B.key c))) b labels g j)
    (hc : (IntegralMixedFramedRootPullback.instructionAt P B.plan (pairFst (B.key c)) b).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient (pairFst (B.key c))) b labels g j HG).rule) :
    let Q := (IntegralMixedFramedRootPullback.instructionAt P B.plan (pairFst (B.key c)) b).source
    let p := geometricPoint B T c w hv b
    (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
    (∀i (hi : i<WordListRecords.count labels), p ⟨i,hi.trans_le HG.1.1⟩=
      IntegralFramedPhysicalBankTerm.env B T hr c w hv (Nat.fromBitsLE (WordList.get labels i))) ∧
    ∀i : Fin ((P).ambient (pairFst (B.key c))+1), WordListRecords.count labels ≤ i.val → i.val≠g →
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂
        (Int.castRingHom ℝ) p=0 := by
  have H := frame_point B T hr c w hv b hb labels g j HG hc
  refine ⟨H.1,?_,H.2.2⟩
  intro i hi
  have HL : Nat.fromBitsLE (WordList.get labels i)<
      (IntegralMixedFramedBankSnapshotBits.atKey P B.plan B.data (B.key c)).count := by
    change _<(IntegralMixedFramedHistoryFamilyBits.family P B.plan B.data).birth (B.key c)
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    exact (HG.1.2 i hi).trans (active_direct B T c b hb).1
  rw [IntegralFramedPhysicalBankTerm.env_chronological B T hr c w hv _ HL]
  simpa only [IntegralMixedFramedHistoryFamilyBits.family_birth] using H.2.1 i hi

end LeanCanny.Encoding.IntegralFramedPhysicalCompanionPoint
