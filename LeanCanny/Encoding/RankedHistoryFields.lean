/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RankedHistoryTask
public import LeanCanny.Encoding.FixedWidthQuery

/-! # Bounded numeric fields in flat history queries

A fixed number of numeric fields use the binary size of a root-dependent
cap as their width. Writers clip malformed values; valid values are read
back exactly. Retargeting preserves one root record and gives a unary word
allowance independent of the number of recursive task replacements.
-/

@[expose] public section
namespace LeanCanny.Encoding.RankedHistoryFields
open Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

variable (cap : List Bool → ℕ) (K : ℕ)

def width (q : List Bool) : ℕ := (cap (RankedHistoryTask.root q)).size

theorem width_unary (hc : BinaryFn cap) : UnaryFn (width cap) := by
  have H : BinaryFn (fun q => cap (RankedHistoryTask.root q)) := hc.comp RankedHistoryTask.root_FP
  exact (UnaryFn.length H.bits_mem_FP).of_eq (fun q => BinaryNatCode.length_encode _)

def clipped (reader : List Bool → List Bool) (q : List Bool) (i : ℕ) : ℕ :=
  min (Nat.fromBitsLE (reader (pair q (BinaryNatCode.encode i)))) (cap (RankedHistoryTask.root q))

def clippedReader (reader : List Bool → List Bool) (p : List Bool) : List Bool :=
  BinaryNatCode.encode (min (Nat.fromBitsLE (reader p)) (cap (RankedHistoryTask.root (pairFst p))))

theorem clippedReader_FP (hc : BinaryFn cap) (reader : List Bool → List Bool) (hr : reader ∈ FP) :
    clippedReader cap reader ∈ FP := by
  have HC : BinaryFn (fun p => cap (RankedHistoryTask.root (pairFst p))) :=
    hc.comp (mem_FP_comp pairFst_mem_FP RankedHistoryTask.root_FP)
  have HR : BinaryFn (fun p => Nat.fromBitsLE (reader p)) := BinaryFn.fromBits hr
  exact mem_FP_of_eq (BinaryFn.ite (HR.le HC) HR HC).bits_mem_FP (fun p => by
    unfold clippedReader
    rw [Nat.min_def])

theorem clippedReader_packet (reader : List Bool → List Bool) (q : List Bool) (i : ℕ) :
    clippedReader cap reader (pair q (BinaryNatCode.encode i)) = BinaryNatCode.encode (clipped cap reader q i) := by
  simp only [clippedReader, clipped, pairFst_pair]

def write (reader : List Bool → List Bool) (q : List Bool) : List Bool :=
  FixedWidthNatVector.encode K (width cap q) (clipped cap reader q)

theorem write_FP (hc : BinaryFn cap) (reader : List Bool → List Bool) (hr : reader ∈ FP) : write cap K reader ∈ FP :=
  FixedWidthNatVector.encode_mem_FP (fun _ => K) (width cap) (clipped cap reader) (UnaryFn.const K)
    (width_unary cap hc) (clippedReader cap reader) (clippedReader_FP cap hc reader hr) (clippedReader_packet cap reader)

theorem write_length (reader : List Bool → List Bool) (q : List Bool) :
    (write cap K reader q).length = K * (cap (RankedHistoryTask.root q)).size :=
  FixedWidthNatVector.length_encode _ _ _

def get (q : List Bool) (i : ℕ) : ℕ :=
  min (FixedWidthQuery.entry (fun _ => K) (width cap) RankedHistoryTask.fields q i) (cap (RankedHistoryTask.root q))

theorem get_le (q : List Bool) (i : ℕ) : get cap K q i ≤ cap (RankedHistoryTask.root q) := min_le_right _ _

def read (p : List Bool) : List Bool :=
  clippedReader cap (FixedWidthQuery.read (fun _ => K) (width cap) RankedHistoryTask.fields) p

theorem read_FP (hc : BinaryFn cap) : read cap K ∈ FP :=
  clippedReader_FP cap hc _ (FixedWidthQuery.read_mem_FP (UnaryFn.const K) (width_unary cap hc) RankedHistoryTask.fields_FP)

theorem read_packet (q : List Bool) (i : ℕ) : read cap K (pair q (BinaryNatCode.encode i)) = BinaryNatCode.encode (get cap K q i) := by
  unfold read clippedReader
  rw [FixedWidthQuery.read_packet]
  simp only [pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem get_retarget (reader : List Bool → List Bool) (b p : List Bool → ℕ) (q : List Bool) (i : ℕ) (hi : i < K) :
    get cap K (RankedHistoryTask.retarget b p (write cap K reader) q) i = clipped cap reader q i := by
  unfold get FixedWidthQuery.entry
  rw [ite_eq_left hi]
  unfold FixedWidthQuery.coordinate
  simp only [RankedHistoryTask.retarget, width, RankedHistoryTask.root_pack, RankedHistoryTask.fields_pack]
  unfold write width
  rw [FixedWidthNatVector.decode_block _ _ _ i hi]
  · exact min_eq_left (min_le_right _ _)
  · exact (min_le_right _ _).trans_lt (Nat.lt_size_self _)

theorem get_retarget_eq (reader : List Bool → List Bool) (b p : List Bool → ℕ) (q : List Bool) (i : ℕ) (hi : i < K)
    (h : Nat.fromBitsLE (reader (pair q (BinaryNatCode.encode i))) ≤ cap (RankedHistoryTask.root q)) :
    get cap K (RankedHistoryTask.retarget b p (write cap K reader) q) i = Nat.fromBitsLE (reader (pair q (BinaryNatCode.encode i))) := by
  rw [get_retarget cap K reader b p q i hi]
  exact min_eq_left h

/-- A temporary packet exposes the original root without retaining the wrapper. -/
def prepared (parent : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (RankedHistoryTask.root (parent q)) q

def unwrapReader (reader : List Bool → List Bool) (z : List Bool) : List Bool :=
  reader (pair (pairSnd (pairFst z)) (pairSnd z))

theorem unwrapReader_FP (reader : List Bool → List Bool) (hr : reader ∈ FP) : unwrapReader reader ∈ FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) hr

def flatten (parent : List Bool → List Bool) (b p : List Bool → ℕ) (reader : List Bool → List Bool) (q : List Bool) : List Bool :=
  RankedHistoryTask.retarget (b ∘ pairSnd) (p ∘ pairSnd) (write cap K (unwrapReader reader)) (prepared parent q)

theorem flatten_FP (hc : BinaryFn cap) (parent : List Bool → List Bool) (hparent : parent ∈ FP)
    (b p : List Bool → ℕ) (hb : BinaryFn b) (hp : BinaryFn p) (reader : List Bool → List Bool) (hr : reader ∈ FP) :
    flatten cap K parent b p reader ∈ FP :=
  mem_FP_comp (f := prepared parent)
    (g := RankedHistoryTask.retarget (b ∘ pairSnd) (p ∘ pairSnd) (write cap K (unwrapReader reader)))
    (mem_FP_pair (mem_FP_comp hparent RankedHistoryTask.root_FP) id_mem_FP)
    (RankedHistoryTask.retarget_FP (hb.comp pairSnd_mem_FP) (hp.comp pairSnd_mem_FP)
      (write_FP cap K hc _ (unwrapReader_FP reader hr)))

theorem flatten_eq_pack (parent : List Bool → List Bool) (b p : List Bool → ℕ) (reader : List Bool → List Bool) (q : List Bool) :
    flatten cap K parent b p reader q = RankedHistoryTask.pack (RankedHistoryTask.root (parent q)) (b q) (p q)
      (write cap K (unwrapReader reader) (prepared parent q)) := by
  unfold flatten RankedHistoryTask.retarget
  simp only [prepared, RankedHistoryTask.root, pairFst_pair, pairSnd_pair, Function.comp_apply]

theorem root_flatten (parent : List Bool → List Bool) (b p : List Bool → ℕ) (reader : List Bool → List Bool) (q : List Bool) :
    RankedHistoryTask.root (flatten cap K parent b p reader q) = RankedHistoryTask.root (parent q) := by
  rw [flatten_eq_pack, RankedHistoryTask.root_pack]

theorem get_flatten (parent : List Bool → List Bool) (b p : List Bool → ℕ) (reader : List Bool → List Bool)
    (q : List Bool) (i : ℕ) (hi : i < K) :
    get cap K (flatten cap K parent b p reader q) i =
      min (Nat.fromBitsLE (reader (pair q (BinaryNatCode.encode i)))) (cap (RankedHistoryTask.root (parent q))) := by
  unfold flatten
  rw [get_retarget cap K _ _ _ _ i hi]
  simp only [clipped, prepared, unwrapReader, RankedHistoryTask.root, pairFst_pair, pairSnd_pair]

theorem flatten_length (parent : List Bool → List Bool) (b p : List Bool → ℕ) (reader : List Bool → List Bool) (q : List Bool) :
    (flatten cap K parent b p reader q).length =
      2 * (RankedHistoryTask.root (parent q)).length + 2 * (b q).size + 2 * (p q).size +
        K * (cap (RankedHistoryTask.root (parent q))).size + 6 := by
  rw [flatten_eq_pack, RankedHistoryTask.pack_length, write_length]
  simp only [prepared, RankedHistoryTask.root, pairFst_pair]

theorem flatten_lower_phase (birthCap : List Bool → ℕ) (P : ℕ) (parent : List Bool → List Bool)
    (b p : List Bool → ℕ) (reader : List Bool → List Bool) (q : List Bool)
    (hb : b q = RankedHistoryTask.birth birthCap (parent q)) (hp : p q < RankedHistoryTask.phase P (parent q)) :
    RankedHistoryTask.rank birthCap P (flatten cap K parent b p reader q) < RankedHistoryTask.rank birthCap P (parent q) := by
  rw [flatten_eq_pack, hb]
  exact RankedHistoryTask.lower_phase birthCap P (parent q) (p q) _ hp

theorem flatten_lower_birth (birthCap : List Bool → ℕ) (P : ℕ) (parent : List Bool → List Bool)
    (b p : List Bool → ℕ) (reader : List Bool → List Bool) (q : List Bool)
    (hb : b q < RankedHistoryTask.birth birthCap (parent q)) (hp : p q < P) :
    RankedHistoryTask.rank birthCap P (flatten cap K parent b p reader q) < RankedHistoryTask.rank birthCap P (parent q) := by
  rw [flatten_eq_pack]
  exact RankedHistoryTask.lower_birth birthCap P (parent q) (b q) (p q) _ hb hp

def bound (q : List Bool) : ℕ := K * (cap q).size

theorem bound_unary (hc : BinaryFn cap) : UnaryFn (bound cap K) :=
  (UnaryFn.const K).mul ((UnaryFn.length hc.bits_mem_FP).of_eq (fun _q => BinaryNatCode.length_encode _))

theorem wordBudget_unary (birthCap : List Bool → ℕ) (P : ℕ) (hb : UnaryFn birthCap) (hc : BinaryFn cap) :
    UnaryFn (RankedHistoryTask.wordBudget birthCap P (bound cap K)) :=
  RankedHistoryTask.wordBudget_unary birthCap P (bound cap K) hb (bound_unary cap K hc)

theorem flatten_length_le (birthCap : List Bool → ℕ) (P : ℕ) (parent : List Bool → List Bool)
    (b p : List Bool → ℕ) (reader : List Bool → List Bool) (q : List Bool)
    (hb : b q ≤ birthCap (RankedHistoryTask.root (parent q))) (hp : p q ≤ P) :
    (flatten cap K parent b p reader q).length ≤ RankedHistoryTask.wordBudget birthCap P (bound cap K) (parent q) := by
  rw [flatten_eq_pack]
  apply RankedHistoryTask.pack_length_le birthCap P (bound cap K) (parent q) (b q) (p q) _ hb hp
  rw [write_length]
  simp only [prepared, RankedHistoryTask.root, pairFst_pair, bound, le_refl]

theorem retarget_iterate_length (birthCap b p : List Bool → ℕ) (P : ℕ) (reader : List Bool → List Bool)
    (hb : ∀ q, b q ≤ birthCap (RankedHistoryTask.root q)) (hp : ∀ q, p q ≤ P) (q : List Bool) (n : ℕ) :
    ((RankedHistoryTask.retarget b p (write cap K reader))^[n] q).length ≤
      q.length + RankedHistoryTask.wordBudget birthCap P (bound cap K) q :=
  RankedHistoryTask.retarget_iterate_length birthCap P (bound cap K) b p (write cap K reader) hb hp
    (fun q => (write_length cap K reader q).le) q n

end LeanCanny.Encoding.RankedHistoryFields
