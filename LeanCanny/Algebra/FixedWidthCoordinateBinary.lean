/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomial
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Binary fixed-width coordinates for arbitrary query words

The bounded reader has a native binary output certificate. Its digit value
depends only on the decoded rank, including for noncanonical rank words.
Invalid spatial coordinates return zero before a binary index is used as
an unbounded unary drop count.
-/

@[expose] public section
namespace LeanCanny.Encoding.FixedWidthQuery
set_option backward.isDefEq.respectTransparency false

theorem coordinate_eq_entry (W : List Bool → ℕ) (word : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    coordinate W word c i = LeanCanny.Algebra.FixedWidthPolynomial.entry (W c) (Nat.fromBitsLE (word c)) i := by
  rw [coordinate, BinaryNat.value_take, LeanCanny.Algebra.FixedWidthPolynomial.drop_value,
    LeanCanny.Algebra.FixedWidthPolynomial.entry_eq_digit]

theorem read_value (A W : List Bool → ℕ) (word : List Bool → List Bool) (q : List Bool) :
    Nat.fromBitsLE (read A W word q) = entry A W word (pairFst q) (Nat.fromBitsLE (pairSnd q)) := by
  by_cases hi : Nat.fromBitsLE (pairSnd q) < A (pairFst q)
  · unfold read entry
    rw [ite_eq_left hi, ite_eq_left hi]
    simp only [BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits, min_eq_left hi.le, coordinate]
  · unfold read entry
    rw [ite_eq_right hi, ite_eq_right hi]
    rfl

theorem entry_binary (A W : List Bool → ℕ) (word : List Bool → List Bool)
    (hA : UnaryFn A) (hW : UnaryFn W) (hw : word ∈ FP) :
    BinaryFn (fun q => entry A W word (pairFst q) (Nat.fromBitsLE (pairSnd q))) :=
  BinaryFn.of_eq (BinaryFn.fromBits (read_mem_FP hA hW hw)) (read_value A W word)

end LeanCanny.Encoding.FixedWidthQuery
