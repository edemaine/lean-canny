/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowQuery
public import LeanCanny.Encoding.IntegralMixedChronologicalMeanCutRaw

/-! # The literal row-query roots preserve their older code and typed cut ABI -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  dimension initial creating

theorem root_candidate (mean : Bool) (z : List Bool) : pairFst (root hn ht ha hR0 mean z)=
    IntegralMixedRoadmapAtomic.candidate (atomic z):=pairFst_pair _ _

theorem root_count (mean : Bool) (z : List Bool) (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedCausalRecordPlanBits.count (root hn ht ha hR0 mean z)=IntegralMixedRoadmapBadProbePacket.count (oldPacket z):=by
  simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    root,raw,pairFst_pair,pairSnd_pair,WordListRecords.count_encode,List.length_append,List.length_singleton,
    IntegralMixedRoadmapBadProbePacket.prefixCodes,List.length_map,List.length_range]
  omega

theorem raw_last (mean : Bool) (z : List Bool) : WordList.get (raw hn ht ha hR0 mean z)
    (IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1)=code hn ht ha hR0 mean z :=by
  have HL : IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1=
      (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)).length:=by
    simp only [IntegralMixedRoadmapBadProbePacket.prefixCodes,List.length_map,List.length_range]
  rw [HL,raw,WordList.get_encode]
  simp

theorem raw_older (mean : Bool) (z : List Bool) (i : ℕ)
    (hi : i<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1) :
    WordList.get (raw hn ht ha hR0 mean z) i=WordList.get (IntegralMixedRoadmapBadProbePacket.raw (oldPacket z)) i :=by
  have HL : i<(IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)).length:=by
    simp only [IntegralMixedRoadmapBadProbePacket.prefixCodes,List.length_map,List.length_range]
    exact hi
  rw [raw,WordList.get_encode,List.getElem?_append_left HL]
  simp only [IntegralMixedRoadmapBadProbePacket.prefixCodes,List.getElem?_map,List.getElem?_range hi,
    Option.map_some,Option.getD_some]

noncomputable def ordinaryData (z : List Bool)
    (H : IntegralMixedChronologicalCutCode.Good (dimension hn ht ha hR0 z) (creating hn ht ha hR0 z)
      (labels z) (offset z) (coordinate z)):=
  IntegralMixedChronologicalCutCode.rawData (dimension hn ht ha hR0 z) (creating hn ht ha hR0 z)
    (labels z) (offset z) (coordinate z) H
noncomputable def meanData (z : List Bool)
    (H : IntegralMixedChronologicalMidpointCode.Good (dimension hn ht ha hR0 z) (creating hn ht ha hR0 z)
      (labels z) (oldProducer false z) (oldProducer true z) (offset z) (coordinate z)):=
  IntegralMixedChronologicalMeanCutCode.rawData (dimension hn ht ha hR0 z) (creating hn ht ha hR0 z)
    (labels z) (oldProducer false z) (oldProducer true z) (offset z) (coordinate z) H

theorem ordinaryData_code (z : List Bool)
    (H : IntegralMixedChronologicalCutCode.Good (dimension hn ht ha hR0 z) (creating hn ht ha hR0 z)
      (labels z) (offset z) (coordinate z)) :
    (ordinaryData hn ht ha hR0 z H).code (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0=code hn ht ha hR0 false z:=by
  simpa only [ordinaryData,code,Bool.false_eq_true,ite_false] using
    IntegralMixedChronologicalCutCode.rawData_code (dimension hn ht ha hR0 z) (creating hn ht ha hR0 z)
      (labels z) (offset z) (coordinate z) H 0 0 0 (by decide)

theorem meanData_code (z : List Bool)
    (H : IntegralMixedChronologicalMidpointCode.Good (dimension hn ht ha hR0 z) (creating hn ht ha hR0 z)
      (labels z) (oldProducer false z) (oldProducer true z) (offset z) (coordinate z)) :
    (meanData hn ht ha hR0 z H).code (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0=code hn ht ha hR0 true z:=by
  simpa only [meanData,code,ite_true,
    IntegralMixedChronologicalCutCode.ordinaryTag_index 0 (by decide)] using
    IntegralMixedChronologicalMeanCutCode.rawData_code (dimension hn ht ha hR0 z) (creating hn ht ha hR0 z)
      (labels z) (oldProducer false z) (oldProducer true z) (offset z) (coordinate z) H
      (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
