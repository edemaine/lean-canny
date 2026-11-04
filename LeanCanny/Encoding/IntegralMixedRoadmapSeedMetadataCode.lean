/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedResamplingLayout
/-! # Every literal depth-zero seed record selects its intended coordinate -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def selected (d a : ℕ) : ℕ:=if a=0 then 0 else if a<d+2 then d-(a-1) else 0

theorem selected_lt (d a : ℕ) : selected d a<d+1 :=by
  unfold selected
  split_ifs <;> omega

theorem seedCodes_length (d : ℕ) : (IntegralMixedRoadmapChain.seedCodes d).length=d+2:=by
  simp only [IntegralMixedRoadmapChain.seedCodes,List.length_append,List.length_singleton,
    IntegralMixedChronologicalCompanionCode.codes,List.length_map,List.length_range]
  have H : WordListRecords.count ([] : List Bool)=0:=WordListRecords.count_encode []
  rw [H]
  omega

theorem seedCode_get (d a : ℕ) (ha : a<d+2) :
    (IntegralMixedRoadmapChain.seedCodes d)[a]?=some
      (IntegralMixedChronologicalFrameCode.code d [] 0 (selected d a)) :=by
  cases a with
  | zero=>simp only [IntegralMixedRoadmapChain.seedCodes,List.singleton_append,List.getElem?_cons_zero,
      IntegralMixedRoadmapChain.seedCode,selected,ite_true]
  | succ a=>
    have H : WordListRecords.count ([] : List Bool)=0:=WordListRecords.count_encode []
    simp only [IntegralMixedRoadmapChain.seedCodes,List.singleton_append,List.getElem?_cons_succ,
      IntegralMixedChronologicalCompanionCode.codes,H,Nat.sub_zero,List.getElem?_map,
      List.getElem?_range (by omega : a<d+1),Option.map_some,selected,
      Nat.succ_ne_zero,ite_false,show a+1<d+2 by omega,ite_true,Nat.add_sub_cancel]

theorem raw_lookup (d a : ℕ)
    (ha : a<WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapSeedResampling.payload d))) :
    WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapSeedResampling.payload d)) a=
      IntegralMixedChronologicalFrameCode.code d [] 0 (selected d a) :=by
  rw [IntegralMixedRoadmapSeedResampling.raw_exact,WordList.get_encode]
  by_cases hs : a<d+2
  · rw [List.getElem?_append_left (by rw [seedCodes_length];exact hs),seedCode_get d a hs]
    rfl
  · have HL : a<(IntegralMixedRoadmapChain.seedCodes d).length+
        (IntegralMixedRoadmapChain.paddingCount d (IntegralMixedRoadmapSeedResampling.payload d)+1):=by
      simpa only [IntegralMixedRoadmapSeedResampling.raw_exact,WordListRecords.count_encode,
        List.length_append,List.length_replicate] using ha
    rw [List.getElem?_append_right (by rw [seedCodes_length];omega),
      List.getElem?_replicate,ite_eq_left (by omega),Option.getD_some]
    unfold selected IntegralMixedRoadmapChain.seedCode
    rw [ite_eq_right (by omega),ite_eq_right hs]

end LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata
