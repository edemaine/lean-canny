/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbePacket
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixRun
/-! # Literal reserved-root readback on the checked canonical raw-table domain

The supplied equality is byte syntax, as provided by Chain.raw_paddedWord.
No malformed raw root is replaced by a re-encoded root, and no full word is
moved between the two roots.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeCanonical
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedRoadmapBadProbePacket
set_option backward.isDefEq.respectTransparency false

theorem prefixCodes_eq (q : List Bool) (codes : List (List Bool)) (last : List Bool)
    (hr : raw q=WordList.encode (codes++[last])) :prefixCodes q=codes:=by
 have HC :count q=codes.length+1:=by
   simp only [count,hr,WordListRecords.count_encode,List.length_append,List.length_singleton]
 unfold prefixCodes
 rw [HC,Nat.add_sub_cancel]
 calc
   (List.range codes.length).map (WordList.get (raw q))=
       (List.range codes.length).map (WordList.get (WordList.encode codes)):=by
     apply List.map_congr_left
     intro i hi
     have HL:=List.mem_range.mp hi
     rw [hr,WordList.get_encode,List.getElem?_append_left HL,←WordList.get_encode]
   _=codes:=by
     simpa only [WordListRecords.decode,WordListRecords.count_encode] using WordListRecords.decode_encode codes

theorem root_eq (q : List Bool) (codes : List (List Bool)) (last : List Bool)
    (hr : raw q=WordList.encode (codes++[last])) :
    root q=IntegralMixedMarkedPrefixRun.reservedRoot (candidate q) codes last []:=by
 unfold root IntegralMixedMarkedPrefixRun.reservedRoot
 rw [hr]

theorem preparedRoot_eq (d : ℕ) (q hint : List Bool) (codes : List (List Bool)) (last : List Bool)
    (hr : raw q=WordList.encode (codes++[last])) :
    preparedRoot d (pair q hint)=IntegralMixedMarkedPrefixRun.reservedRoot (candidate q) codes
      (probe d (pair q hint)) []:=by
 unfold preparedRoot preparedRaw IntegralMixedMarkedPrefixRun.reservedRoot
 simp only [pairFst_pair,prefixCodes_eq q codes last hr]

theorem count_eq (q : List Bool) (codes : List (List Bool)) (last : List Bool)
    (hr : raw q=WordList.encode (codes++[last])) :count q=codes.length+1:=by
 simp only [count,hr,WordListRecords.count_encode,List.length_append,List.length_singleton]

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeCanonical
