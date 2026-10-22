/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FixedWidthNatVector
public import LeanCanny.Tactic.PolyTime

/-! # FP fixed-width vector writing from coordinate access

A polynomial number of fixed-width coordinates can be written bit by bit
using a uniform FP binary coordinate reader. Oversized coordinates are
truncated to the requested width; the earlier round trip applies when they fit.
-/

@[expose] public section

namespace LeanCanny.Encoding.FixedWidthNatVector


theorem encode_mem_FP (A W : List Bool → ℕ) (e : List Bool → ℕ → ℕ)
    (hA : UnaryFn A) (hW : UnaryFn W) (read : List Bool → List Bool) (hr : read ∈ FP)
    (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = BinaryNatCode.encode (e c i)) :
    (fun c => encode (A c) (W c) (e c)) ∈ FP := by
  let query := fun z => pair (pairFst z)
    (BinaryNatCode.encode ((pairSnd z).length / W (pairFst z)))
  have hq : query ∈ FP := mem_FP_pair pairFst_mem_FP (bits_mem_FP (UnaryFn.index.div hW.lift))
  let G := fun z => [(read (query z))[((pairSnd z).length % W (pairFst z))]?.getD false]
  have hG : G ∈ FP := by
    have h := (FPPred.getBit (mem_FP_comp hq hr) (UnaryFn.index.mod hW.lift)).flag_mem_FP
    exact mem_FP_of_eq h (fun _ => rfl)
  let b := fun c k => (e c (k / W c)).testBit (k % W c)
  have hspec : ∀ c k, G (pair c (List.replicate k true)) = [b c k] := by
    intro c k
    simp only [G, query, pairFst_pair, pairSnd_pair, List.length_replicate, he]
    rw [← BinaryNat.fromBitsLE_testBit, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have H := bitwise_mem_FP (hA.mul hW).mem_FP hG hspec
  refine mem_FP_of_eq H ?_
  intro c
  apply List.ext_getElem
  · simp [encode]
  · intro k hk hk'
    simp only [List.getElem_map, List.getElem_range, encode, List.getElem_ofFn, b]

end LeanCanny.Encoding.FixedWidthNatVector
