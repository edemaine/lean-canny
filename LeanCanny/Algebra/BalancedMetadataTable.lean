/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedParameterContext
public import LeanCanny.Encoding.FixedWidthQuery

/-! # Fixed-width degree and direction metadata for balanced nodes

The original-input field is `pair source (pair unaryWidth tableBits)`. A node
has inorder key `2^height*(2*index+1)`; cells `2*key` and `2*key+1` store its
degree and direction. Lookup is FP on all words and returns at most the
supplied width, including malformed and undersized tables.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedMetadataTable
open LeanCanny.Encoding
open Turing.MultiTapeTM

def source : List Bool → List Bool := pairFst
def width (c : List Bool) : ℕ := (pairFst (pairSnd c)).length
def bits (c : List Bool) : List Bool := pairSnd (pairSnd c)
def count (c : List Bool) : ℕ := (bits c).length

def key (h i : ℕ) : ℕ := 2 ^ h * (2 * i + 1)
def cell (direction : Bool) (p : List Bool) : ℕ :=
  2 * key (BalancedParameterContext.height p) (BalancedParameterContext.index p) + if direction then 1 else 0

def query (direction : Bool) (p : List Bool) : List Bool :=
  pair (BalancedParameterContext.original p) (BinaryNatCode.encode (cell direction p))

def read (direction : Bool) : List Bool → List Bool := FixedWidthQuery.read count width bits ∘ query direction
def order (p : List Bool) : ℕ := Nat.fromBitsLE (read false p)
def direction (p : List Bool) : ℕ := Nat.fromBitsLE (read true p)

theorem key_zero (i : ℕ) : key 0 i = 2 * i + 1 := by simp [key]
theorem key_succ (h i : ℕ) : key (h + 1) i = 2 * key h i := by unfold key; rw [pow_succ]; ring

theorem key_injective (h i k j : ℕ) (he : key h i = key k j) : h = k ∧ i = j := by
  induction h generalizing k i j with
  | zero =>
    cases k with
    | zero => simp only [key_zero] at he; exact ⟨rfl, by omega⟩
    | succ k => rw [key_zero, key_succ] at he; omega
  | succ h ih =>
    cases k with
    | zero => rw [key_succ, key_zero] at he; omega
    | succ k =>
      rw [key_succ, key_succ] at he
      obtain ⟨hk, hij⟩ := ih i k j (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) he)
      exact ⟨congrArg Nat.succ hk, hij⟩

theorem key_lt (H h i : ℕ) (hh : h ≤ H) (hi : i < 2 ^ (H - h)) : key h i < 2 ^ (H + 1) := by
  have hlt : 2 * i + 1 < 2 * 2 ^ (H - h) := by omega
  have hm := Nat.mul_lt_mul_of_pos_left hlt (show 0 < 2 ^ h by positivity)
  apply hm.trans_eq
  calc
    2 ^ h * (2 * 2 ^ (H - h)) = 2 * (2 ^ h * 2 ^ (H - h)) := by ring
    _ = 2 * 2 ^ H := by rw [← pow_add, show h + (H - h) = H by omega]
    _ = 2 ^ (H + 1) := by rw [pow_succ]; omega

/-- Enough cells for the degree/direction fields of every padded tree node. -/
def capacity (n : ℕ) : ℕ := 8 * (n + 1)

theorem cell_lt_capacity (which : Bool) (n h i : ℕ) (hh : h ≤ n.size) (hi : i < 2 ^ (n.size - h)) :
    2 * key h i + (if which then 1 else 0) < capacity n := by
  have hk := key_lt n.size h i hh hi
  rw [pow_succ] at hk
  have hw := FiniteAnnihilatorTree.width_bound n
  unfold capacity
  cases which <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem capacity_unary {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (fun c => capacity (n c)) :=
  (UnaryFn.const 8).mul (hn.add (UnaryFn.const 1))

attribute [local irreducible] BinaryNat.normalize

theorem source_FP : source ∈ FP := pairFst_mem_FP
theorem width_unary : UnaryFn width := UnaryFn.length (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem bits_FP : bits ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem count_unary : UnaryFn count := UnaryFn.length bits_FP

theorem cell_binary (which : Bool) : BinaryFn (cell which) := by
  have hi := BinaryFn.fromBits BalancedParameterContext.indexWord_FP
  have hh := (BinaryFn.const 2).powUnary BalancedParameterContext.height_unary
  have hk := hh.mul (((BinaryFn.const 2).mul hi).add (BinaryFn.const 1))
  exact ((BinaryFn.const 2).mul hk).add (BinaryFn.const (if which then 1 else 0))

theorem query_FP (which : Bool) : query which ∈ FP :=
  mem_FP_pair BalancedParameterContext.original_FP (cell_binary which).bits_mem_FP

theorem read_FP (which : Bool) : read which ∈ FP :=
  mem_FP_comp (query_FP which) (FixedWidthQuery.read_mem_FP count_unary width_unary bits_FP)

theorem read_length_le (which : Bool) (p : List Bool) :
    (read which p).length ≤ width (BalancedParameterContext.original p) := by
  unfold read FixedWidthQuery.read query
  dsimp only [Function.comp_apply]
  simp only [pairFst_pair]
  split_ifs
  · exact (BinaryNat.normalize_length_le _).trans (List.length_take_le _ _)
  · exact Nat.zero_le _

theorem width_le_length (c : List Bool) : width c ≤ c.length :=
  (pairFst_length_le (pairSnd c)).trans (pairSnd_length_le c)

theorem read_eq_packet (which : Bool) (p : List Bool) :
    read which p = read which (BalancedParameterContext.packet (BalancedParameterContext.original p)
      (BalancedParameterContext.height p) (BalancedParameterContext.index p)) := by
  simp only [read, Function.comp_apply, query, cell, BalancedParameterContext.original_packet,
    BalancedParameterContext.height_packet, BalancedParameterContext.index_packet]

def frame (c : List Bool) (A W : ℕ) (values : ℕ → ℕ) : List Bool :=
  pair c (pair (List.replicate W true) (FixedWidthNatVector.encode A W values))

theorem frame_length (c : List Bool) (A W : ℕ) (values : ℕ → ℕ) :
    (frame c A W values).length = 2 * c.length + 2 * W + A * W + 4 := by
  simp only [frame, pair_length, List.length_replicate, FixedWidthNatVector.length_encode]
  omega

theorem source_frame (c : List Bool) (A W : ℕ) (values : ℕ → ℕ) : source (frame c A W values) = c := by
  simp only [source, frame, pairFst_pair]

theorem width_frame (c : List Bool) (A W : ℕ) (values : ℕ → ℕ) : width (frame c A W values) = W := by
  simp only [width, frame, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem bits_frame (c : List Bool) (A W : ℕ) (values : ℕ → ℕ) :
    bits (frame c A W values) = FixedWidthNatVector.encode A W values := by
  simp only [bits, frame, pairSnd_pair]

theorem read_frame (which : Bool) (c : List Bool) (A W h i : ℕ) (values : ℕ → ℕ)
    (hW : 0 < W) (hi : 2 * key h i + (if which then 1 else 0) < A)
    (hv : values (2 * key h i + if which then 1 else 0) < 2 ^ W) :
    read which (BalancedParameterContext.packet (frame c A W values) h i) =
      BinaryNatCode.encode (values (2 * key h i + if which then 1 else 0)) := by
  unfold read query
  simp only [Function.comp_apply, cell, BalancedParameterContext.original_packet,
    BalancedParameterContext.height_packet, BalancedParameterContext.index_packet]
  rw [FixedWidthQuery.read_packet]
  have hA : A ≤ count (frame c A W values) := by
    simp only [count, bits_frame, FixedWidthNatVector.length_encode]
    exact Nat.le_mul_of_pos_right _ hW
  rw [FixedWidthQuery.entry, ite_eq_left (hi.trans_le hA)]
  simp only [FixedWidthQuery.coordinate, width_frame, bits_frame]
  rw [FixedWidthNatVector.decode_block A W values _ hi hv]

end LeanCanny.Algebra.BalancedMetadataTable
