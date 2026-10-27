/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberMoments
public import LeanCanny.Encoding.SparseFeatureRecords

/-! # Short sparse derivative-sign records in algebraic fibers

Twice the binary degree width supplies enough factor slots for the sparse
spanning monomials. Zero slots denote unit factors; nonzero slots select a
binary derivative order, with large codes clamped to the final feature.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberRecords
open LeanCanny.Algebra LeanCanny.Computation BoundedAlgebraicSlice

noncomputable def slots (F : Family) (c : List Bool) : ℕ := 2 * (F.degree c).size
noncomputable def width (F : Family) (c : List Bool) : ℕ := (F.degree c).size + 2
noncomputable def length (F : Family) (c : List Bool) : ℕ := slots F c * width F c

theorem size_unary {F : Family} (A : F.Access) : UnaryFn (fun c => (F.degree c).size) :=
  (UnaryFn.length A.degree_binary.bits_mem_FP).of_eq (fun c => BinaryNatCode.length_encode (F.degree c))
theorem slots_unary {F : Family} (A : F.Access) : UnaryFn (slots F) := (UnaryFn.const 2).mul (size_unary A)
theorem width_unary {F : Family} (A : F.Access) : UnaryFn (width F) := (size_unary A).add (UnaryFn.const 2)
theorem length_unary {F : Family} (A : F.Access) : UnaryFn (length F) := (slots_unary A).mul (width_unary A)
theorem width_pos (F : Family) (c : List Bool) : 0 < width F c := by unfold width; omega

noncomputable def recordSlots (F : Family) (z : List Bool) : ℕ := (pairSnd z).length / width F (pairFst z)
theorem recordSlots_unary {F : Family} (A : F.Access) : UnaryFn (recordSlots F) :=
  (UnaryFn.length pairSnd_mem_FP).div ((width_unary A).comp pairFst_mem_FP)
theorem recordSlots_packet (F : Family) (c r : List Bool) (hr : r.length = length F c) :
    recordSlots F (pair c r) = slots F c := by
  simp only [recordSlots, pairFst_pair, pairSnd_pair, hr, length]
  exact Nat.mul_div_cancel _ (width_pos F c)

noncomputable def slot (F : Family) (z : List Bool) (i : ℕ) : ℕ :=
  FixedWidthQuery.entry (recordSlots F) (width F ∘ pairFst) pairSnd z i
noncomputable def read (F : Family) : List Bool → List Bool :=
  FixedWidthQuery.read (recordSlots F) (width F ∘ pairFst) pairSnd
theorem read_FP {F : Family} (A : F.Access) : read F ∈ FP :=
  FixedWidthQuery.read_mem_FP (recordSlots_unary A) ((width_unary A).comp pairFst_mem_FP) pairSnd_mem_FP
theorem read_packet (F : Family) (z : List Bool) (i : ℕ) :
    read F (pair z (BinaryNatCode.encode i)) = BinaryNatCode.encode (slot F z i) :=
  FixedWidthQuery.read_packet _ _ _ z i

noncomputable def order (F : Family) (z : List Bool) (i : ℕ) : ℕ := min (slot F z i - 1) (F.degree (pairFst z))
noncomputable def orderRead (F : Family) (t : List Bool) : List Bool :=
  BinaryNatCode.encode (min (Nat.fromBitsLE (read F t) - 1) (F.degree (pairFst (pairFst t))))
theorem orderRead_FP {F : Family} (A : F.Access) : orderRead F ∈ FP := by
  have hx := (BinaryFn.fromBits (read_FP A)).sub (BinaryFn.const 1)
  have hd := A.degree_binary.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have hm : BinaryFn (fun t => min (Nat.fromBitsLE (read F t) - 1) (F.degree (pairFst (pairFst t)))) :=
    BinaryFn.of_eq (BinaryFn.ite (hx.le hd) hx hd) (fun _ => by simp only [min_def, Function.comp_apply])
  exact hm.bits_mem_FP
theorem orderRead_packet (F : Family) (z : List Bool) (i : ℕ) :
    orderRead F (pair z (BinaryNatCode.encode i)) = BinaryNatCode.encode (order F z i) := by
  rw [orderRead, read_packet]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair, order]

noncomputable def exponent (F : Family) (z : List Bool) (i : ℕ) : Fin 3 := if slot F z i = 0 then 0 else 1
noncomputable def exponentRead (F : Family) (t : List Bool) : List Bool :=
  if read F t = [] then BinaryNatCode.encode 0 else BinaryNatCode.encode 1
theorem exponentRead_FP {F : Family} (A : F.Access) : exponentRead F ∈ FP :=
  (Brackets.stringEq_fppred (read_FP A) (constFn_mem_FP [])).ite_mem_FP
    (constFn_mem_FP (BinaryNatCode.encode 0)) (constFn_mem_FP (BinaryNatCode.encode 1))
theorem exponentRead_packet (F : Family) (z : List Bool) (i : ℕ) :
    exponentRead F (pair z (BinaryNatCode.encode i)) = BinaryNatCode.encode (exponent F z i).val := by
  rw [exponentRead, read_packet]
  have hz : BinaryNatCode.encode (slot F z i) = [] ↔ slot F z i = 0 := BinaryNat.bits_eq_nil_iff _
  simp only [hz, exponent]
  split_ifs <;> rfl

theorem slot_coordinate (F : Family) (c r : List Bool) (i : ℕ) (hi : i < recordSlots F (pair c r)) :
    slot F (pair c r) i = SparseFeatureRecords.coordinate (width F c) r i := by
  rw [slot, FixedWidthQuery.entry, ite_eq_left hi]
  simp only [FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair, pairSnd_pair, SparseFeatureRecords.coordinate]

theorem feature_fits (F : Family) (c : List Bool) : F.degree c + 1 < 2 ^ width F c := by
  unfold width
  rw [pow_add]
  have hd := Nat.lt_size_self (F.degree c)
  have hp := Nat.two_pow_pos (F.degree c).size
  norm_num
  omega

end LeanCanny.Encoding.BoundedAlgebraicFiberRecords
