/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateAffineRecord

/-! # Native doubled coordinate directions

Two-bit signed blocks encode doubled coordinate objectives and normals.
Their exact decoder and polynomial-time writer retain the original layout.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineRecord
open LeanCanny.Computation
open scoped Classical

def unsigned (n r : ℕ) := FixedWidthNatVector.encode ((n + 1) * n) 2
  (fun j => 2 * CoordinateAffineRecord.entry n r j)
def record (n r : ℕ) := PositiveAffineRecord.encode ((n + 1) * n) 2 (unsigned n r)

lemma integer_record (n r j : ℕ) (hj : j < (n + 1) * n) :
    FlatAffineFullSourceTower.integer 2 (record n r) j = 2 * (CoordinateAffineRecord.entry n r j : ℤ) := by
  rw [record, PositiveAffineRecord.integer_encode _ _ _ _ hj]
  unfold FixedWidthQuery.coordinate unsigned
  have he : 2 * CoordinateAffineRecord.entry n r j < 2 ^ 2 := by
    have := CoordinateAffineRecord.entry_lt n r j
    norm_num at this ⊢
    omega
  have H := FixedWidthNatVector.decode_block ((n + 1) * n) 2
    (fun j => 2 * CoordinateAffineRecord.entry n r j) j hj he
  simpa only [id_eq, Nat.cast_mul, Nat.cast_ofNat] using congrArg (fun k : ℕ => (k : ℤ)) H

lemma integer_double (n r j : ℕ) (hj : j < (n + 1) * n) :
    FlatAffineFullSourceTower.integer 2 (record n r) j =
      2 * FlatAffineFullSourceTower.integer 1 (CoordinateAffineRecord.record n r) j := by
  rw [integer_record n r j hj, CoordinateAffineRecord.integer_record n r j hj]

def read (n r : List Bool → ℕ) (q : List Bool) :=
  BinaryNatCode.encode (2 * CoordinateAffineRecord.entry (n (pairFst q)) (r (pairFst q)) (Nat.fromBitsLE (pairSnd q)))

theorem read_FP {n r : List Bool → ℕ} (hn : UnaryFn n) (hr : BinaryFn r) : read n r ∈ FP := by
  have he : BinaryFn (fun q => CoordinateAffineRecord.entry (n (pairFst q)) (r (pairFst q)) (Nat.fromBitsLE (pairSnd q))) :=
    BinaryFn.of_bits (CoordinateAffineRecord.read_FP hn hr)
  exact ((BinaryFn.const 2).mul he).bits_mem_FP

theorem record_FP {n r : List Bool → ℕ} (hn : UnaryFn n) (hr : BinaryFn r) :
    (fun c => record (n c) (r c)) ∈ FP := by
  have ht := (hn.add (UnaryFn.const 1)).mul hn
  have hu : (fun c => unsigned (n c) (r c)) ∈ FP :=
    FixedWidthNatVector.encode_mem_FP _ _ _ ht (UnaryFn.const 2) (read n r) (read_FP hn hr)
      (fun c j => by simp only [read, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  exact PositiveAffineRecord.encode_FP ht (UnaryFn.const 2) hu

lemma length_record (n r : ℕ) : (record n r).length = (n + 1) * n * 4 :=
  PositiveAffineRecord.length_encode _ _ _

lemma objective (n : ℕ) (r i : Fin n) :
    FlatAffineFullSourceTower.integer 2 (record n r.val) i.val = 2 * (if i = r then 1 else 0) := by
  rw [integer_double n r.val i.val (by nlinarith [i.isLt]), CoordinateAffineRecord.objective]

lemma normal (n r : ℕ) (j i : Fin n) :
    FlatAffineFullSourceTower.integer 2 (record n r) (j.succ.val * n + i.val) =
      2 * (if i = j then 1 else 0) := by
  rw [integer_double n r _ (by have := j.isLt; have := i.isLt; simp only [Fin.val_succ]; nlinarith),
    CoordinateAffineRecord.normal]

end LeanCanny.Encoding.CoordinateDoubleAffineRecord
