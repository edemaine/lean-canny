/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.WordListFP
public import LeanCanny.Computation.PolyTimeRange
/-! # Total native counts and decoding of original word-list records -/
@[expose] public section
namespace LeanCanny.Encoding.WordListRecords
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def tail (p : List Bool) := pairSnd^[min (Nat.fromBitsLE (pairSnd p)) (pairFst p).length] (pairFst p)

theorem tail_FP : tail ∈ FP := by
  have HC : UnaryFn (fun p => min (Nat.fromBitsLE (pairSnd p)) (pairFst p).length) :=
    UnaryFn.fromBitsLE_min pairSnd_mem_FP (UnaryFn.length pairFst_mem_FP)
  have HE := iterate_mem_FP pairSnd_mem_FP pairFst_mem_FP (HC.replicate_mem_FP false) id_mem_FP
    (by intro p n _; exact (WordList.tail_iterate_length (pairFst p) n).trans (pairFst_length_le p))
  exact mem_FP_of_eq HE (fun p => by simp only [List.length_replicate]; rfl)

def indexPacket (p : List Bool) := pair (pairFst p) (BinaryNatCode.encode (pairSnd p).length)
theorem indexPacket_FP : indexPacket ∈ FP :=
  mem_FP_pair pairFst_mem_FP (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP

def count (w : List Bool) : ℕ :=
  ((Finset.range w.length).filter fun i => tail (pair w (BinaryNatCode.encode i)) ≠ []).card

theorem count_unary : UnaryFn count := by
  have HT := mem_FP_comp indexPacket_FP tail_FP
  have HL : UnaryFn (fun p => (tail (indexPacket p)).length) := UnaryFn.length HT
  have HP : FPPred (fun p => tail (indexPacket p) ≠ []) := (FPPred.eq HL (UnaryFn.const 0)).not.of_iff
    (fun p => by simp only [List.length_eq_zero_iff])
  have HC := UnaryFn.count (UnaryFn.length id_mem_FP) HP
  apply HC.of_eq
  intro w
  simp only [count, indexPacket, pairFst_pair, pairSnd_pair, List.length_replicate, id_eq]

theorem count_le_length (w : List Bool) : count w ≤ w.length :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

theorem tail_packet (w : List Bool) (i : ℕ) : tail (pair w (BinaryNatCode.encode i)) = pairSnd^[min i w.length] w := by
  simp only [tail, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem encode_eq_nil (ws : List (List Bool)) : WordList.encode ws = [] ↔ ws = [] := by
  cases ws with
  | nil => constructor <;> intro _ <;> rfl
  | cons w ws =>
    constructor
    · intro he
      have H := congrArg List.length he
      simp only [WordList.encode, pair_length, List.length_nil] at H
      omega
    · intro he; cases he

theorem tail_encode_nonempty (ws : List (List Bool)) (i : ℕ) :
    tail (pair (WordList.encode ws) (BinaryNatCode.encode i)) ≠ [] ↔ i < ws.length := by
  rw [tail_packet, WordList.tail_iterate]
  have HE (j : ℕ) : ws.drop j = [] ↔ ws.length ≤ j := by
    rw [← List.length_eq_zero_iff, List.length_drop, Nat.sub_eq_zero_iff_le]
  rw [ne_eq, encode_eq_nil, HE]
  have HL := WordList.count_le_length ws
  omega

theorem count_encode (ws : List (List Bool)) : count (WordList.encode ws) = ws.length := by
  unfold count
  have HE : ((Finset.range (WordList.encode ws).length).filter fun i =>
      tail (pair (WordList.encode ws) (BinaryNatCode.encode i)) ≠ []) = Finset.range ws.length := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, tail_encode_nonempty]
    constructor
    · exact And.right
    · intro hi; exact ⟨hi.trans_le (WordList.count_le_length ws), hi⟩
  rw [HE, Finset.card_range]

def decode (w : List Bool) := (List.range (count w)).map (WordList.get w)

theorem length_decode (w : List Bool) : (decode w).length = count w := by simp only [decode, List.length_map, List.length_range]

theorem decode_encode (ws : List (List Bool)) : decode (WordList.encode ws) = ws := by
  apply List.ext_getElem
  · rw [length_decode, count_encode]
  · intro i hi hi'
    simp only [decode, List.getElem_map, List.getElem_range, WordList.get_encode,
      List.getElem?_eq_getElem hi', Option.getD_some]
end LeanCanny.Encoding.WordListRecords
