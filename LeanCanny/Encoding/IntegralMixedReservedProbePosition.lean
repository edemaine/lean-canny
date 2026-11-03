/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainLedger
public import LeanCanny.Encoding.IntegralMixedCausalRecordPlan
/-! # The checked padded chronological table ends in its actual reserved probe -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedReservedProbePosition
open IntegralMixedRoadmapRecordChain
set_option backward.isDefEq.respectTransparency false

def beforeProbe {n T labels : ℕ} (r : Records n T labels) (seed : Word T):=
 (r.codes++List.replicate (recordBound n-r.codes.length) seed).map Subtype.val

theorem beforeProbe_length {n T labels : ℕ} (r : Records n T labels) (seed : Word T) :
    (beforeProbe r seed).length=recordBound n:=by
 have H:=r.codes_length_le
 simp only [beforeProbe,List.length_map,List.length_append,List.length_replicate]
 omega

theorem paddedWord_last {n T labels : ℕ} (r : Records n T labels) (seed probe : Word T) :
    r.paddedWord seed probe=WordList.encode (beforeProbe r seed++[probe.val]):=by
 simp only [Records.paddedWord,Records.paddedCodes,List.map_append,List.map_cons,List.map_nil,beforeProbe]

theorem root_last {n T labels : ℕ} (r : Records n T labels) (seed probe : Word T)
    (candidate metadata : List Bool) :
    IntegralMixedCausalRecordPlanBits.records (r.root seed probe candidate metadata)=
      WordList.encode (beforeProbe r seed++[probe.val]):=by
 simp only [IntegralMixedCausalRecordPlanBits.records,Records.root,pairFst_pair,pairSnd_pair]
 exact paddedWord_last r seed probe

theorem checked_last {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapChain.Checked n B sourceCap initial C q) :
    IntegralMixedRoadmapChain.raw q=WordList.encode
      (beforeProbe (IntegralMixedRoadmapChain.records h)
        (IntegralMixedRoadmapChain.seed n initial C ⟨0,by omega⟩)++[IntegralMixedRoadmapChain.probe q]):=by
 rw [IntegralMixedRoadmapChain.raw_paddedWord h]
 exact paddedWord_last _ _ _

end LeanCanny.Encoding.IntegralMixedReservedProbePosition
