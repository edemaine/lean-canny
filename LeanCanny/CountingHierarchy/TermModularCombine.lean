/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.TermModularFrames
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-! # A native bounded combine step for modular expression-tree evaluation -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.TermModular

open LeanCanny.Encoding LeanCanny.ETR Turing.MultiTapeTM
open Brackets

 def combineBits (P : Parameters) (packet : List Bool) : List Bool :=
  let z := pairFst packet
  let child := pairFst (pairSnd packet)
  let parent := pairSnd (pairSnd packet)
  pair (consNode (raw child) (raw parent))
    (encList encNat (finish P (pair z child) :: values parent))

 theorem combineBits_FP (P : Parameters) (hP : Access P) : combineBits P ∈ FP := by
  have hchild : (fun p => pairFst (pairSnd p)) ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hparent : (fun p => pairSnd (pairSnd p)) ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hpacket := mem_FP_pair pairFst_mem_FP hchild
  have hvalue := (finish_binary P hP).comp (FP.computable hpacket)
  have hvalues := values_FP.comp (FP.computable hparent)
  have hlist := ComputableTidilyInPolyTime.cons' hvalue hvalues
  have hencoded := hlist.encoded
  have hraw := consNode_mem_FP (mem_FP_comp hchild pairFst_mem_FP) (mem_FP_comp hparent pairFst_mem_FP)
  exact mem_FP_of_eq (mem_FP_pair hraw hencoded) (fun _ => rfl)

 theorem combineBits_code (P : Parameters) (z : List Bool) (child parent : List Data) :
    combineBits P (pair z (pair (code P z child) (code P z parent))) = code P z (NNF.combine child parent) := by
  simp only [combineBits, pairFst_pair, pairSnd_pair, raw_code, values_code, finish_code,
    consNode_toBits]
  simp only [code, NNF.combine, List.map_cons]

 theorem code_empty_length (P : Parameters) (z : List Bool) : (code P z []).length = 6 := by
  simp [code, Data.size_empty]

 theorem code_growth (P : Parameters) (z : List Bool) (child parent : List Data) :
    (code P z (NNF.combine child parent)).length ≤
      (code P z child).length + (code P z parent).length + (2 * (cap P z).size + 1) := by
  have hsize := Nat.size_le_size (value_lt (P.prime z) (P.coordinate z) (.l child)).le
  change (value (P.prime z) (P.coordinate z) (.l child)).size ≤ (cap P z).size at hsize
  simp only [code, NNF.combine, Data.cons_size, List.map_cons, pair_length, Data.length_toBits,
    length_encList, List.map_cons, List.sum_cons, encNat_apply, Nat.size_eq_bits_len]
  omega

end LeanCanny.CountingHierarchy.TermModular
