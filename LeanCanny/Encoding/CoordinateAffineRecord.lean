/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.PositiveAffineRecord
public import LeanCanny.Computation.PolyTimeBinaryArithmetic

/-! # Native signed records for coordinate objectives and normals

Row zero is the selected coordinate objective. The remaining rows are the
coordinate normals. Each signed coefficient occupies two one-bit blocks.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateAffineRecord
open LeanCanny.Computation
open scoped Classical

def entry (n r j : ℕ) : ℕ :=
  if j / n = 0 then (if j % n = r then 1 else 0)
  else if j / n - 1 = j % n then 1 else 0

lemma entry_lt (n r j : ℕ) : entry n r j < 2 ^ 1 := by
  unfold entry
  split_ifs <;> decide

def unsigned (n r : ℕ) : List Bool :=
  FixedWidthNatVector.encode ((n + 1) * n) 1 (entry n r)

def record (n r : ℕ) : List Bool :=
  PositiveAffineRecord.encode ((n + 1) * n) 1 (unsigned n r)

lemma length_record (n r : ℕ) : (record n r).length = (n + 1) * n * 2 := by
  exact PositiveAffineRecord.length_encode _ _ _

lemma integer_record (n r j : ℕ) (hj : j < (n + 1) * n) :
    FlatAffineFullSourceTower.integer 1 (record n r) j = (entry n r j : ℤ) := by
  rw [record, PositiveAffineRecord.integer_encode _ _ _ _ hj]
  unfold FixedWidthQuery.coordinate unsigned
  simpa only [id_eq] using congrArg (fun k : ℕ => (k : ℤ))
    (FixedWidthNatVector.decode_block ((n + 1) * n) 1 (entry n r) j hj (entry_lt n r j))

lemma objective (n : ℕ) (r i : Fin n) :
    FlatAffineFullSourceTower.integer 1 (record n r.val) i.val = if i = r then 1 else 0 := by
  rw [integer_record n r.val i.val (by nlinarith [i.isLt])]
  simp [entry, Nat.div_eq_of_lt i.isLt, Nat.mod_eq_of_lt i.isLt, Fin.ext_iff]

lemma normal (n r : ℕ) (j i : Fin n) :
    FlatAffineFullSourceTower.integer 1 (record n r) (j.succ.val * n + i.val) =
      if i = j then 1 else 0 := by
  rw [integer_record n r _ (by have := j.isLt; have := i.isLt; simp only [Fin.val_succ]; nlinarith)]
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hd : (j.succ.val * n + i.val) / n = j.val + 1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt i.isLt]
    simp
  have hm : (j.succ.val * n + i.val) % n = i.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  simp only [entry, hd, hm, Nat.add_one_ne_zero, Nat.add_sub_cancel, Fin.ext_iff]
  by_cases h : j.val = i.val
  · rw [h]; simp
  · simp [h, Ne.symm h]

def read (n r : List Bool → ℕ) (q : List Bool) : List Bool :=
  BinaryNatCode.encode (entry (n (pairFst q)) (r (pairFst q)) (Nat.fromBitsLE (pairSnd q)))

theorem read_FP {n r : List Bool → ℕ} (hn : UnaryFn n) (hr : BinaryFn r) : read n r ∈ FP := by
  have hi := BinaryFn.fromBits pairSnd_mem_FP
  have hN := (BinaryFn.ofUnary hn).comp pairFst_mem_FP
  have hR := hr.comp pairFst_mem_FP
  have hrow := hi.div hN
  have hcol := hi.mod hN
  have he : BinaryFn (fun q => entry (n (pairFst q)) (r (pairFst q)) (Nat.fromBitsLE (pairSnd q))) :=
    BinaryFn.ite (hrow.eq (BinaryFn.const 0))
      (BinaryFn.ite (hcol.eq hR) (BinaryFn.const 1) (BinaryFn.const 0))
      (BinaryFn.ite ((hrow.sub (BinaryFn.const 1)).eq hcol) (BinaryFn.const 1) (BinaryFn.const 0))
  exact he.bits_mem_FP

theorem record_FP {n r : List Bool → ℕ} (hn : UnaryFn n) (hr : BinaryFn r) :
    (fun c => record (n c) (r c)) ∈ FP := by
  have htotal := (hn.add (UnaryFn.const 1)).mul hn
  have hu : (fun c => unsigned (n c) (r c)) ∈ FP :=
    FixedWidthNatVector.encode_mem_FP _ _ _ htotal (UnaryFn.const 1) (read n r) (read_FP hn hr)
      (fun c j => by simp only [read, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  exact PositiveAffineRecord.encode_FP htotal (UnaryFn.const 1) hu

end LeanCanny.Encoding.CoordinateAffineRecord
