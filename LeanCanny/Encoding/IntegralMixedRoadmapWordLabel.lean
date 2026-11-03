/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicSize
/-! # Fixed-width labels retain entire actual atomic vertex bytes

The second bracket field holds padding. The native first-field reader
therefore recovers the complete original vertex without a length oracle.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapWordLabel
open LeanCanny.Algebra LeanCanny.Computation

def encode (w : ℕ) (q : List Bool):=pair q (List.replicate (2*(w-q.length)) false)
def decode (r : List Bool):=pairFst r

theorem decode_FP : decode∈FP:=pairFst_mem_FP

theorem encode_FP {w : List Bool→ℕ} {q : List Bool→List Bool} (hw : UnaryFn w) (hq : q∈FP) :
    (fun u=>encode (w u) (q u))∈FP:=mem_FP_pair hq
  (((UnaryFn.const 2).mul (hw.sub (UnaryFn.length hq))).replicate_mem_FP false)

theorem decode_encode (w : ℕ) (q : List Bool) : decode (encode w q)=q:=pairFst_pair _ _

theorem encode_length (w : ℕ) (q : List Bool) (hq : q.length≤w) : (encode w q).length=2*w+2 :=by
  simp only [encode,pair_length,List.length_replicate]
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapWordLabel
