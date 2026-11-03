/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainTruncation
/-! # Canonical history completion uses a terminal seed birth

Replacing a query probe by the empty-frame seed makes all remaining records
one honest seed tail. Meaningful history and its labels stay fixed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapChain
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical

theorem compiledCodes_seed_tail (n : ℕ) (q : List Bool) (hp : probe q=seedCode n) :
    compiledCodes n q=meaningfulCodes n q++List.replicate (paddingCount n q+1) (seedCode n) :=by
  simp only [compiledCodes,hp,List.replicate_add,List.replicate_one,List.append_assoc]

theorem raw_seed_tail {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) (hp : probe q=seedCode n) :
    raw q=WordList.encode (meaningfulCodes n q++List.replicate (paddingCount n q+1) (seedCode n)) :=by
  rw [hq.2.2.2.2.2.1,compiled,compiledCodes_seed_tail n q hp]

theorem prefix_seed_probe (n : ℕ) (q : List Bool) (k : ℕ) :
    probe (prefixPayload n q k (seedCode n))=seedCode n :=
  completePayload_probe n _ _

theorem append_seed_probe (n : ℕ) (q l r : List Bool) (side : Bool) :
    probe (appendPayload n q l r side (seedCode n))=seedCode n :=
  completePayload_probe n _ _

end LeanCanny.Encoding.IntegralMixedRoadmapChain
