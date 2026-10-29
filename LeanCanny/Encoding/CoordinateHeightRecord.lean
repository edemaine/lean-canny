/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffinePrefix

/-! # Native records for coordinate heights and exact midpoints

A copied height uses a doubled coordinate normal; a midpoint uses an
undoubled normal on each ancestral block. Both records fit signed two-bit
entries, and their stage references use the tower's ordinary clamping rule.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateHeightRecord
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def vector (n index scale : ℕ) : List Bool :=
  PositiveAffineRecord.encode n 2 (FixedWidthNatVector.encode n 2 (fun i => if i = index then scale else 0))

lemma integer_vector (n index scale i : ℕ) (hi : i < n) (hs : scale < 4) :
    FlatAffineFullSourceTower.integer 2 (vector n index scale) i = if i = index then (scale : ℤ) else 0 := by
  rw [vector, PositiveAffineRecord.integer_encode _ _ _ _ hi]
  unfold FixedWidthQuery.coordinate
  have he : (if i = index then scale else 0) < 2 ^ 2 := by split_ifs <;> omega
  have H := FixedWidthNatVector.decode_block n 2 (fun i => if i = index then scale else 0) i hi he
  simpa only [id_eq, Nat.cast_ite, Nat.cast_zero] using congrArg (fun k : ℕ => (k : ℤ)) H

def vectorRead (index scale : List Bool → ℕ) (q : List Bool) : List Bool :=
  BinaryNatCode.encode (if Nat.fromBitsLE (pairSnd q) = index (pairFst q) then scale (pairFst q) else 0)

theorem vectorRead_FP {index scale : List Bool → ℕ} (hi : BinaryFn index) (hs : BinaryFn scale) :
    vectorRead index scale ∈ FP :=
  (BinaryFn.ite ((BinaryFn.fromBits pairSnd_mem_FP).eq (hi.comp pairFst_mem_FP))
    (hs.comp pairFst_mem_FP) (BinaryFn.const 0)).bits_mem_FP

theorem vector_FP {n index scale : List Bool → ℕ} (hn : UnaryFn n) (hi : BinaryFn index) (hs : BinaryFn scale) :
    (fun c => vector (n c) (index c) (scale c)) ∈ FP := by
  have hu : (fun c => FixedWidthNatVector.encode (n c) 2 (fun i => if i = index c then scale c else 0)) ∈ FP :=
    FixedWidthNatVector.encode_mem_FP _ _ _ hn (UnaryFn.const 2) (vectorRead index scale) (vectorRead_FP hi hs)
      (fun c j => by simp only [vectorRead, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  exact PositiveAffineRecord.encode_FP hn (UnaryFn.const 2) hu

def height (n index ancestor : ℕ) : List Bool :=
  pair [true, true, false] (pair (BinaryNatCode.encode ancestor) (pair [] (pair (vector n index 2) [])))

def midpoint (n index left right : ℕ) : List Bool :=
  pair [true, false, true]
    (pair (BinaryNatCode.encode left) (pair (BinaryNatCode.encode right) (pair (vector n index 1) [])))

theorem height_FP {n index ancestor : List Bool → ℕ} (hn : UnaryFn n) (hi : BinaryFn index) (ha : BinaryFn ancestor) :
    (fun c => height (n c) (index c) (ancestor c)) ∈ FP :=
  mem_FP_pair (constFn_mem_FP _) (mem_FP_pair ha.bits_mem_FP
    (mem_FP_pair (constFn_mem_FP []) (mem_FP_pair (vector_FP hn hi (BinaryFn.const 2)) (constFn_mem_FP []))))

theorem midpoint_FP {n index left right : List Bool → ℕ}
    (hn : UnaryFn n) (hi : BinaryFn index) (hl : BinaryFn left) (hr : BinaryFn right) :
    (fun c => midpoint (n c) (index c) (left c) (right c)) ∈ FP :=
  mem_FP_pair (constFn_mem_FP _) (mem_FP_pair hl.bits_mem_FP
    (mem_FP_pair hr.bits_mem_FP (mem_FP_pair (vector_FP hn hi (BinaryFn.const 1)) (constFn_mem_FP []))))

lemma height_tag (n index ancestor : ℕ) : FlatAffineFullSourceTower.tag (height n index ancestor) = 1 := by
  simp [height, FlatAffineFullSourceTower.tag, FlatAffineFullSourceTower.flags]
  rfl

lemma midpoint_tag (n index left right : ℕ) : FlatAffineFullSourceTower.tag (midpoint n index left right) = 2 := by
  simp [midpoint, FlatAffineFullSourceTower.tag, FlatAffineFullSourceTower.flags]
  rfl

lemma height_normal (n index ancestor i : ℕ) (hi : i < n) :
    FlatAffineFullSourceTower.integer 2 (FlatAffineFullSourceTower.normal (height n index ancestor)) i =
      if i = index then 2 else 0 := by
  simp only [height, FlatAffineFullSourceTower.normal, pairSnd_pair, pairFst_pair]
  exact integer_vector n index 2 i hi (by decide)

lemma midpoint_normal (n index left right i : ℕ) (hi : i < n) :
    FlatAffineFullSourceTower.integer 2 (FlatAffineFullSourceTower.normal (midpoint n index left right)) i =
      if i = index then 1 else 0 := by
  simp only [midpoint, FlatAffineFullSourceTower.normal, pairSnd_pair, pairFst_pair]
  exact integer_vector n index 1 i hi (by decide)

end LeanCanny.Encoding.CoordinateHeightRecord
