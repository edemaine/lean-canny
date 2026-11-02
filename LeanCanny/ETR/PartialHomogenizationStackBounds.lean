/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.PartialHomogenizationFrameBounds
/-! # Complete additive stack accounting for the annotated tree pass -/
@[expose] public section
namespace LeanCanny.ETR.PartialHomogenizationData
open LeanCanny.Encoding

def frameCode (k D L : ℕ) (xs : List Data) : List Bool :=
  pair (Data.l xs).toBits
    (pair (Data.l (xs.map (fun d => Codec.unary (degree k D d)))).toBits
      (Data.l (xs.map (bounded k D L))).toBits)

theorem frameCode_empty (k D L : ℕ) : (frameCode k D L []).length = 14 := by
  simp [frameCode,pair_length,Data.length_toBits,Data.size_empty]

theorem frameCode_growth (k D L : ℕ) (child parent : List Data) :
    (frameCode k D L (NNF.combine child parent)).length ≤
      (frameCode k D L child).length + (frameCode k D L parent).length + (40*D+L+100) := by
  have H := bounded_node_size k D L child
  have HD := degree_le k D (.l child)
  simp only [frameCode,NNF.combine,List.map_cons,pair_length,Data.length_toBits,
    Data.cons_size,Codec.unary_size]
  omega

end LeanCanny.ETR.PartialHomogenizationData
