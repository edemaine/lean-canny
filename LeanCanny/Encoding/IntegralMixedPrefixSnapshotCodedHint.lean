/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotCodedFactor
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbePacket
/-! # A chosen ordinary factor has the actual bounded four-field hint -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalCutCode
open LeanCanny.Algebra LeanCanny.Geometry IntegralMixedHistory IntegralMixedRelativeCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem raw_offset (n birth : ℕ) (labels : List Bool) (g j : ℕ) (h : Good n birth labels g j) (Q : ℤ) (hQ : Q≠0):
    ((rawData n birth labels g j h).rule Q hQ).critical.offset.val=WordListRecords.count labels+1:=by
 have HE:=IntegralMixedChronologicalSweepFrame.pointData_offset
   (IntegralMixedChronologicalFrameCode.descriptor n birth labels h.1) (raw_fit n birth labels g j h)
   ⟨g,h.2.2.1⟩ ⟨j,h.2.2.2.2⟩ (raw_free_g n birth labels g j h) (raw_free_j n birth labels g j h)
 exact HE.trans (congrArg (fun k=>k+1) (IntegralMixedChronologicalFrameCode.descriptor_length n birth labels h.1))

end LeanCanny.Encoding.IntegralMixedChronologicalCutCode
namespace LeanCanny.Algebra.IntegralMixedPrefixSnapshot
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedRelativeCuts
open IntegralMixedRoadmapBadProbePacket
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem coordinate_lt {n : ℕ} (P : SpatialSource n) (r : IntegralMixedCriticalSweep.Rule n) (c : Kind P r):
    IntegralMixedSweepRetarget.coordinateIndex r c<n-r.critical.offset.val+1:=by
 cases c <;>exact Fin.isLt _

theorem Data.coded_hint (d : Data) (base : List Bool) (values : ℕ→ℝ) (a : ℝ) (code : List Bool)
    (initial : ℕ) (hcount :0<count base) (hbirth :d.birth=creating initial base)
    (hl :producer false base<d.birth) (hr :producer true base<d.birth)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (d.ambient+1) d.source.degree≤2^d.width)
    (h :d.CodedFactor (labels base) values a code) :
    ∃hint,HintGood d.ambient initial d.width (pair base hint) ∧probe d.ambient (pair base hint)=code ∧
      Nat.fromBitsLE (field 3 (pair base hint))≤IntegralMixedExceptionalBounds.auxiliaryCap (d.ambient+1) d.source.degree:=by
 obtain ⟨hready,φ,c,_,_,ho,_,hc⟩:=h
 let r:=d.rule (labels base) hready
 let tag:=IntegralMixedCutRecordConstructor.tagIndex (IntegralMixedSweepRetarget.tag r c)
 let j:=WordListRecords.count (labels base)+1+IntegralMixedSweepRetarget.coordinateIndex r c
 let choice:=IntegralMixedSweepRetarget.choiceIndex r c
 let degree:=selectedDegree d.state hready.1 r φ c
 let hint:=WordList.encode [BinaryNatCode.encode tag,BinaryNatCode.encode j,BinaryNatCode.encode choice,BinaryNatCode.encode degree]
 have HE :∀i<4,Nat.fromBitsLE (field i (pair base hint))=([tag,j,choice,degree][i]?.getD 0):=by
   intro i hi
   interval_cases i <;>simp only [field,hint,pairSnd_pair,WordList.get_encode,List.getElem?_cons_zero,
     List.getElem?_cons_succ,Option.getD_some,BinaryNatCode.encode,Nat.fromBitsLE_bits]
 have HJ :j<d.ambient+1:=by
   have HI:=coordinate_lt d.source r c
   have HO :r.critical.offset.val=WordListRecords.count (labels base)+1:=
     IntegralMixedChronologicalCutCode.raw_offset d.ambient d.birth (labels base) _ _ (d.rawGood _ hready) _ _
   dsimp only [j]
   rw [HO] at HI
   have HO' :WordListRecords.count (labels base)+1<d.ambient+1:=hready.2.2
   omega
 have HC :choice≤2^d.width:=(IntegralMixedCutRecordConstructor.choice_le d.source r c).trans hcap
 have HD :degree≤2^d.width:=(selectedDegree_bound d.state hready.1 r φ c).trans hcap
 refine ⟨hint,?_,?_,?_⟩
 · simp only [HintGood,pairFst_pair]
   rw [HE 0 (by decide),HE 1 (by decide),HE 2 (by decide),HE 3 (by decide)]
   simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
   refine ⟨hcount,?_,ho,?_,HJ,HC,HD,?_,?_⟩
   · exact hbirth ▸ hready.2.1
   · dsimp only [j];omega
   · exact hl.trans_eq hbirth
   · exact hr.trans_eq hbirth
 · unfold probe
   simp only [pairFst_pair]
   rw [HE 0 (by decide),HE 1 (by decide),HE 2 (by decide),HE 3 (by decide)]
   simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
   exact (IntegralMixedChronologicalCutCode.raw_chosenCode_actual (labels base) _ (d.rawGood _ hready)
     d.source _ _ c degree).symm.trans hc.symm

 · rw [HE 3 (by decide)]
   exact selectedDegree_bound d.state hready.1 r φ c

end LeanCanny.Algebra.IntegralMixedPrefixSnapshot
