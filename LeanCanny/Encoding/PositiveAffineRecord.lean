/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FixedWidthQuery
public import LeanCanny.Encoding.FlatAffineFullSourceTower
public import LeanCanny.Computation.PolyTimeBinaryArithmetic

/-! # Unsigned objective words in signed affine records

Interleaving zero negative blocks preserves each unsigned coordinate under
the actual signed tower decoder. The total FP writer pads short input words
and truncates long ones to the prescribed dimension and width.
-/

@[expose] public section
namespace LeanCanny.Encoding.PositiveAffineRecord
open LeanCanny.Computation
open scoped Classical

/-- Zero padding outside the source dimension also makes the reader total. -/
def entry (n W : ℕ) (record : List Bool) (j : ℕ) : ℕ :=
  if j % 2 = 0 then FixedWidthQuery.entry (fun _ => n) (fun _ => W) id record (j / 2) else 0

def encode (n W : ℕ) (record : List Bool) : List Bool :=
  FixedWidthNatVector.encode (2 * n) W (entry n W record)

theorem length_encode (n W : ℕ) (record : List Bool) : (encode n W record).length = n * (2 * W) := by
  rw [encode, FixedWidthNatVector.length_encode]
  ring

theorem integer_encode (n W : ℕ) (record : List Bool) (i : ℕ) (hi : i < n) :
    FlatAffineFullSourceTower.integer W (encode n W record) i =
      (FixedWidthQuery.coordinate (fun _ => W) id record i : ℤ) := by
  have he (j : ℕ) : entry n W record j < 2 ^ W := by
    unfold entry FixedWidthQuery.entry FixedWidthQuery.coordinate
    split_ifs
    · exact (Nat.fromBitsLE_lt_pow_length _).trans_le
        (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))
    all_goals exact Nat.two_pow_pos W
  have hp := FixedWidthNatVector.decode_block (2 * n) W (entry n W record) (2 * i) (by omega) (he (2 * i))
  have hn := FixedWidthNatVector.decode_block (2 * n) W (entry n W record) (2 * i + 1) (by omega) (he (2 * i + 1))
  have hmul : i * (2 * W) = 2 * i * W := by ring
  have hadd : 2 * i * W + W = (2 * i + 1) * W := by ring
  unfold FlatAffineFullSourceTower.integer encode
  rw [hmul, hadd, hp, hn]
  simp [entry, FixedWidthQuery.entry, hi, Nat.add_mod]

def read (n W : List Bool → ℕ) (record : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd q) % 2 = 0 then
    FixedWidthQuery.read n W record (pair (pairFst q) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q) / 2)))
  else []

theorem read_FP {n W : List Bool → ℕ} {record : List Bool → List Bool}
    (hn : UnaryFn n) (hW : UnaryFn W) (hr : record ∈ FP) : read n W record ∈ FP := by
  have hi := BinaryFn.fromBits pairSnd_mem_FP
  have hp := (hi.mod (BinaryFn.const 2)).eq (BinaryFn.const 0)
  have hq := mem_FP_pair pairFst_mem_FP (hi.div (BinaryFn.const 2)).bits_mem_FP
  exact hp.ite_mem_FP (mem_FP_comp hq (FixedWidthQuery.read_mem_FP hn hW hr)) (constFn_mem_FP [])

theorem read_packet (n W : List Bool → ℕ) (record : List Bool → List Bool) (c : List Bool) (j : ℕ) :
    read n W record (pair c (BinaryNatCode.encode j)) = BinaryNatCode.encode (entry (n c) (W c) (record c) j) := by
  simp only [read, pairFst_pair, pairSnd_pair, show Nat.fromBitsLE (BinaryNatCode.encode j) = j from Nat.fromBitsLE_bits j]
  split_ifs with hj
  · rw [FixedWidthQuery.read_packet]
    simp only [entry, hj, ite_true, FixedWidthQuery.entry, FixedWidthQuery.coordinate, id_eq]
  · simp only [entry, hj, ite_false, BinaryNatCode.encode]
    rfl

theorem encode_FP {n W : List Bool → ℕ} {record : List Bool → List Bool}
    (hn : UnaryFn n) (hW : UnaryFn W) (hr : record ∈ FP) :
    (fun c => encode (n c) (W c) (record c)) ∈ FP :=
  FixedWidthNatVector.encode_mem_FP _ _ _ ((UnaryFn.const 2).mul hn) hW
    (read n W record) (read_FP hn hW hr) (read_packet n W record)

end LeanCanny.Encoding.PositiveAffineRecord
