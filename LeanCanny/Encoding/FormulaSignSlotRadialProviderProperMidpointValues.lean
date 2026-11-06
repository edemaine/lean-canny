/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointCaptures
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEqualitySemantics
/-! # Every accepted midpoint capture reads its own actual critical coordinate -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalCompanionPoint
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (BK : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
  (hr : IntegralMixedFramedHeaderBits.Represents BK.parameters BK.plan BK.data T)
include hr
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "S"=>IntegralFramedPhysicalBankTerm.input BK
theorem midpoint_frame_env (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w)
    (b : ℕ) (hb : Active BK T c b) (labels : List Bool) (aIndex bIndex g j : ℕ)
    (HG : IntegralMixedChronologicalMidpointCode.Good ((P).ambient (pairFst ((BK).key c))) b labels aIndex bIndex g j)
    (hc : (IntegralMixedFramedRootPullback.instructionAt P (BK).plan (pairFst ((BK).key c)) b).command=
      .critical (IntegralMixedChronologicalMidpointCode.rawData ((P).ambient (pairFst ((BK).key c))) b labels aIndex bIndex g j HG).rule) :
    let Q:=(IntegralMixedFramedRootPullback.instructionAt P (BK).plan (pairFst ((BK).key c)) b).source
    let p:=geometricPoint BK T c w hv b
    let value:=(fun i (_hi : i<b)=>IntegralFramedPhysicalBankTerm.env BK T hr c w hv i)
    (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
    (∀i (hi : i<WordListRecords.count labels),p ⟨i,hi.trans_le HG.1.1⟩=
      value (Nat.fromBitsLE (WordList.get labels i)) (HG.1.2 i hi)) ∧
    p ⟨WordListRecords.count labels,by have H1:=HG.2.2.2.1;have H2:=HG.2.2.2.2.1;omega⟩=
      (value aIndex HG.2.1+value bIndex HG.2.2.1)/2 ∧
    ∀ (i : Fin ((P).ambient (pairFst ((BK).key c))+1)), Nat.le (WordListRecords.count labels+1) (Fin.val i) → Ne (Fin.val i) g →
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂
        (Int.castRingHom ℝ) p=0 :=by
  have HF:=midpoint_frame_point BK T hr c w hv b hb labels aIndex bIndex g j HG hc
  have HE (i : ℕ) (hi : i<b) :
      IntegralFramedPhysicalSquare.point P (BK).plan (BK).data (BK).nodes (BK).factor (BK).seed (BK).bounds
        (BK).key (BK).positive c w hv
        ⟨IntegralMixedFramedHistoryFamilyBits.prefixLength P ((BK).key c)-1-i,by
          rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
          have HB:=(active_direct BK T c b hb).1
          omega⟩=
      IntegralFramedPhysicalBankTerm.env BK T hr c w hv i :=by
    have HL : i<(IntegralMixedFramedBankSnapshotBits.atKey P (BK).plan (BK).data ((BK).key c)).count:=by
      change i<(IntegralMixedFramedHistoryFamilyBits.family P (BK).plan (BK).data).birth ((BK).key c)
      rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
      exact hi.trans (active_direct BK T c b hb).1
    rw [IntegralFramedPhysicalBankTerm.env_chronological BK T hr c w hv i HL]
    simp only [IntegralMixedFramedHistoryFamilyBits.family_birth]
  refine ⟨HF.1,?_,?_,HF.2.2.2⟩
  · intro i hi
    exact (HF.2.1 i hi).trans (HE _ (HG.1.2 i hi))
  · exact HF.2.2.1.trans (congrArg₂ (fun a b : ℝ=>(a+b)/2) (HE aIndex HG.2.1) (HE bIndex HG.2.2.1))
end LeanCanny.Encoding.IntegralFramedPhysicalCompanionPoint

namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T"=>FormulaSignSlotRadialProviderRecordPlan.tables
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family

theorem critical_field (q : List Bool) (hv : Valid q) (b : ℕ) (hb : Active (context q) b) :
    field q hv b=geometricPoint (context q) (word q) (full_valid q hv) b
      ⟨selected (context q) b,selected_lt _ _ hb⟩ :=by
  have HF:=IntegralFramedPhysicalCriticalGuardScan.active_guard input P D H T (B).nodes (B).factor
    (B).seed (B).bounds (B).key critical_count bank_represents
    (context q) (word q) (full_valid q hv) (valid_critical q hv).2 b
    (IntegralFramedPhysicalCompanionPoint.active_direct B T _ _ hb).1 hb
  change IntegralFramedPhysicalCompanionPoint.retained B T bank_represents (context q) (word q)
    (full_valid q hv) b hb=_ at HF
  have HS:=IntegralFramedPhysicalCompanionPoint.selected_block B T bank_represents
    (context q) (word q) (full_valid q hv) b hb
  have HE:=IntegralFramedPhysicalCompanionPoint.retained_env B T bank_represents
    (context q) (word q) (full_valid q hv) b hb
  exact HE.symm.trans (HF.trans HS)

theorem native_full_prefix (q : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (context q))=
      FormulaSignSlotRadialProviderRecordPlan.fullCount (root q) :=by
  have HE:=FormulaSignSlotRadialProviderFieldEquality.count_eq (context q)
  have HB:=IntegralMixedFramedHistoryFamilyBits.family_birth P D H ((B).key (context q))
  change (IntegralMixedFramedHistoryFamilyBits.family P D H).birth ((B).key (context q))=_ at HE
  exact HB.symm.trans (by simpa only [context,pairFst_pair] using HE)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic

namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProper
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedRoadmapProper
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T"=>FormulaSignSlotRadialProviderRecordPlan.tables
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "N"=>FormulaSignSlotRadialProviderAtomic.initial
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank

private theorem active_of_command (p : IntegralCriticalHistoryTask.Parameters)
    (d : IntegralMixedFramedHistoryFamilyBits.Plan p) (h : IntegralMixedFramedHistoryFamilyBits.Data p d)
    (ts : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents p d h ts)
    (key : List Bool→List Bool) (c : List Bool) (b : ℕ)
    (hb : b<IntegralMixedFramedHistoryFamilyBits.prefixLength p (key c))
    (r : IntegralMixedHistory.CriticalRule (p.ambient (pairFst (key c))))
    (hc : (IntegralMixedFramedRootPullback.instructionAt p d (pairFst (key c)) b).command=.critical r) :
    IntegralMixedFramedCriticalGuardBits.Active p ts (IntegralFramedPhysicalCriticalGuardTest.keyDatum key)
      IntegralFramedPhysicalCriticalGuardScan.stage (pair c (List.replicate b true)) :=by
  constructor
  · simpa only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
      pairFst_pair,pairSnd_pair,List.length_replicate] using hb
  · have HE:=IntegralMixedFramedCriticalGuardBits.header_actual p d h ts hr
      (fun _=>key c) (fun _=>b) []
    have HH : IntegralMixedFramedCriticalGuardBits.header ts
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum key) IntegralFramedPhysicalCriticalGuardScan.stage
        (pair c (List.replicate b true))=
        IntegralMixedCommandHeaderBits.command (IntegralMixedFramedRootPullback.instructionAt p d
          (pairFst (key c)) b).command:=by
      simpa only [IntegralMixedFramedCriticalGuardBits.header,IntegralFramedPhysicalCriticalGuardTest.keyDatum,
        IntegralFramedPhysicalCriticalGuardScan.stage,pairFst_pair,pairSnd_pair,List.length_replicate] using HE
    rw [HH,hc]
    rfl


theorem midpoint_capture_active (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    FormulaSignSlotRadialProviderAtomic.Active (FormulaSignSlotRadialProviderAtomic.context q)
      (midFirst (D q) (N q) q+i) :=by
  have HF:=midpoint_companion_fit q hv hd i hi
  have HB : midFirst (D q) (N q) q+i=FormulaSignSlotRadialProviderRecordPlan.count
      (FormulaSignSlotRadialProviderAtomic.root q)+(midRawIndex (D q) q+1+i):=by
    have HN : FormulaSignSlotRadialProviderRecordPlan.count (FormulaSignSlotRadialProviderAtomic.root q)=N q:=rfl
    rw [HN]
    simp only [midFirst,midBirth,baseBirth,IntegralMixedRoadmapChain.birth,midRawIndex,
      FormulaSignSlotRadialProviderAtomic.payload,IntegralMixedRoadmapAtomic.payload]
    omega
  have HBound : midFirst (D q) (N q) q+i<IntegralMixedFramedHistoryFamilyBits.prefixLength P
      ((B).key (FormulaSignSlotRadialProviderAtomic.context q)):=by
    rw [FormulaSignSlotRadialProviderAtomic.native_full_prefix,HB,
      FormulaSignSlotRadialProviderRecordPlan.fullCount,IntegralMixedCausalRecordPlanBits.count,
      FormulaSignSlotRadialProviderAtomic.root_records]
    omega
  exact active_of_command P (B).plan (B).data T FormulaSignSlotRadialProviderAtomic.bank_represents
    (B).key _ _ HBound _ (midpoint_companion_context_command q hv hd i hi)

theorem midpoint_capture_field (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    FormulaSignSlotRadialProviderAtomic.field q hv (midFirst (D q) (N q) q+i)=
      FormulaSignSlotRadialProviderAtomic.geometricPoint (FormulaSignSlotRadialProviderAtomic.context q)
        (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv)
        (midFirst (D q) (N q) q+i) ⟨D q-i,by rw [FormulaSignSlotRadialProviderAtomic.native_dimension];omega⟩ :=by
  have HA:=midpoint_capture_active q hv hd i hi
  have HE:=FormulaSignSlotRadialProviderAtomic.critical_field q hv _ HA
  have HI : (⟨FormulaSignSlotRadialProviderAtomic.selected (FormulaSignSlotRadialProviderAtomic.context q)
      (midFirst (D q) (N q) q+i),FormulaSignSlotRadialProviderAtomic.selected_lt _ _ HA⟩ :
      Fin ((P).ambient (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context q)))+1))=
      ⟨D q-i,by rw [FormulaSignSlotRadialProviderAtomic.native_dimension];omega⟩ :=
    Fin.ext (midpoint_capture_selected q hv hd i hi)
  exact HE.trans (congrArg (FormulaSignSlotRadialProviderAtomic.geometricPoint
    (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv) (midFirst (D q) (N q) q+i)) HI)

theorem midpoint_capture_geometry (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (i : ℕ) (hi : i<captureCount (D q) q) :
    let b:=midFirst (D q) (N q) q+i
    let hg:=midpoint_companion_context_good q hv hd i hi
    let Q:=(IntegralMixedFramedRootPullback.instructionAt P (B).plan
      (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context q))) b).source
    let p:=FormulaSignSlotRadialProviderAtomic.geometricPoint (FormulaSignSlotRadialProviderAtomic.context q)
      (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv) b
    (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
    (∀j (hj : j<WordListRecords.count (labels q)),p ⟨j,hj.trans_le hg.1.1⟩=
      FormulaSignSlotRadialProviderAtomic.field q hv (Nat.fromBitsLE (WordList.get (labels q) j))) ∧
    p ⟨WordListRecords.count (labels q),by have H1:=hg.2.2.2.1;have H2:=hg.2.2.2.2.1;omega⟩=
      (FormulaSignSlotRadialProviderAtomic.field q hv (producer false q)+
        FormulaSignSlotRadialProviderAtomic.field q hv (producer true q))/2 ∧
    ∀j : Fin ((P).ambient (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context q)))+1),
      WordListRecords.count (labels q)+1≤j.val →j.val≠levelIndex q+1 →
      (MvPolynomial.pderiv j (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂
        (Int.castRingHom ℝ) p=0 :=by
  exact IntegralFramedPhysicalCompanionPoint.midpoint_frame_env B T FormulaSignSlotRadialProviderAtomic.bank_represents
    (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv) (midFirst (D q) (N q) q+i)
    (midpoint_capture_active q hv hd i hi) (labels q) (producer false q) (producer true q)
    (levelIndex q+1) (D q-i) (midpoint_companion_context_good q hv hd i hi)
    (midpoint_companion_context_command q hv hd i hi)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProper
