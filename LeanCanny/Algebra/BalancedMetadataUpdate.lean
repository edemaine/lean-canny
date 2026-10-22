/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedMetadataTable
public import LeanCanny.Encoding.FixedWidthWrite

/-! # Fixed-size native updates to balanced degree and direction tables

Replacement keeps the source and width, and writes exactly the existing
number of complete cells. Thus repeated updates of a canonical frame keep
its length. Every other in-range decoded cell is preserved, without a
promise about the original table values.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedMetadataTable
open LeanCanny.Encoding
open BalancedParameterContext (packet)

def cells (f : List Bool) : ℕ := count f / width f

def replace (f : List Bool) (r v : ℕ) : List Bool :=
  frame (source f) (cells f) (width f)
    (fun k => if k = r then v else FixedWidthQuery.entry cells width bits f k)

attribute [local irreducible] BinaryNat.normalize read

theorem cells_unary : UnaryFn cells := count_unary.div width_unary

theorem replace_mem_FP {f : List Bool → List Bool} {r v : List Bool → ℕ}
    (hf : f ∈ FP) (hr : BinaryFn r) (hv : BinaryFn v) :
    (fun p => replace (f p) (r p) (v p)) ∈ FP := by
  have hA : UnaryFn (cells ∘ f) := cells_unary.comp hf
  have hW : UnaryFn (width ∘ f) := width_unary.comp hf
  have ht := mem_FP_comp hf bits_FP
  have hw := FixedWidthQuery.write_mem_FP hA hW ht hr hv
  have h := mem_FP_pair (mem_FP_comp hf source_FP)
    (mem_FP_pair (hW.replicate_mem_FP true) hw)
  exact mem_FP_of_eq h (fun p => by
    simp only [replace, frame, FixedWidthQuery.write, FixedWidthQuery.entry,
      FixedWidthQuery.coordinate, Function.comp_apply])

theorem cells_frame (c : List Bool) (A W : ℕ) (values : ℕ → ℕ) (hW : 0 < W) :
    cells (frame c A W values) = A := by
  simp only [cells, count, bits_frame, FixedWidthNatVector.length_encode, width_frame]
  exact Nat.mul_div_cancel A hW

theorem source_replace (f : List Bool) (r v : ℕ) : source (replace f r v) = source f :=
  source_frame _ _ _ _

theorem width_replace (f : List Bool) (r v : ℕ) : width (replace f r v) = width f :=
  width_frame _ _ _ _

theorem cells_replace (f : List Bool) (r v : ℕ) : cells (replace f r v) = cells f := by
  by_cases hW : 0 < width f
  · exact cells_frame _ _ _ _ hW
  · have hw : width f = 0 := by omega
    simp only [replace, cells, count, bits_frame, FixedWidthNatVector.length_encode,
      width_frame, hw, Nat.mul_zero, Nat.div_zero]

theorem replace_length (f : List Bool) (r v : ℕ) :
    (replace f r v).length = 2 * (source f).length + 2 * width f + cells f * width f + 4 :=
  frame_length _ _ _ _

theorem replace_twice_length (f : List Bool) (r v s w : ℕ) :
    (replace (replace f r v) s w).length = (replace f r v).length := by
  rw [replace_length, source_replace, width_replace, cells_replace, replace_length]

theorem replace_length_le (f : List Bool) (r v : ℕ) : (replace f r v).length ≤ 5 * f.length + 4 := by
  have hs := pairFst_length_le f
  have hw := width_le_length f
  have hb : count f ≤ f.length := (pairSnd_length_le (pairSnd f)).trans (pairSnd_length_le f)
  have hc : cells f * width f ≤ count f := Nat.div_mul_le_self (count f) (width f)
  rw [replace_length]
  change (pairFst f).length ≤ f.length at hs
  change 2 * (pairFst f).length + 2 * width f + cells f * width f + 4 ≤ _
  omega

theorem replace_frame_length (c : List Bool) (A W r v : ℕ) (values : ℕ → ℕ) (hW : 0 < W) :
    (replace (frame c A W values) r v).length = (frame c A W values).length := by
  rw [replace_length, source_frame, width_frame, cells_frame _ _ _ _ hW, frame_length]

theorem read_eq_entry (which : Bool) (f : List Bool) (h i : ℕ)
    (hk : 2 * key h i + (if which then 1 else 0) < cells f) :
    read which (packet f h i) = BinaryNatCode.encode
      (FixedWidthQuery.entry cells width bits f (2 * key h i + if which then 1 else 0)) := by
  have hk' := hk.trans_le (Nat.div_le_self (count f) (width f))
  unfold read
  simp only [Function.comp_apply, query, cell, BalancedParameterContext.original_packet,
    BalancedParameterContext.height_packet, BalancedParameterContext.index_packet]
  rw [FixedWidthQuery.read_packet]
  simp only [FixedWidthQuery.entry, hk, hk', ite_true]

theorem read_replace (which : Bool) (f : List Bool) (r v h i : ℕ)
    (hW : 0 < width f) (hk : 2 * key h i + (if which then 1 else 0) < cells f)
    (hv : v < 2 ^ width f) :
    read which (packet (replace f r v) h i) =
      if 2 * key h i + (if which then 1 else 0) = r then BinaryNatCode.encode v
      else read which (packet f h i) := by
  have hf : (if 2 * key h i + (if which then 1 else 0) = r then v
      else FixedWidthQuery.entry cells width bits f (2 * key h i + if which then 1 else 0)) < 2 ^ width f := by
    split_ifs <;> first | exact hv | exact FixedWidthQuery.entry_lt cells width bits f _
  rw [replace, read_frame which _ _ _ _ _ _ hW hk hf, read_eq_entry which f h i hk]
  split_ifs <;> rfl

theorem order_replace_direction (f : List Bool) (r v h i : ℕ)
    (hW : 0 < width f) (hk : 2 * key h i < cells f) (hv : v < 2 ^ width f) :
    order (packet (replace f (2 * r + 1) v) h i) = order (packet f h i) := by
  unfold order
  rw [read_replace false f (2 * r + 1) v h i hW (by simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using hk) hv]
  rw [ite_eq_right (by simp only [Bool.false_eq_true, ite_false]; omega)]

theorem direction_replace_other (f : List Bool) (r v h i : ℕ)
    (hW : 0 < width f) (hk : 2 * key h i + 1 < cells f) (hv : v < 2 ^ width f)
    (hne : key h i ≠ r) :
    direction (packet (replace f (2 * r + 1) v) h i) = direction (packet f h i) := by
  unfold direction
  rw [read_replace true f (2 * r + 1) v h i hW (by simpa only [ite_true] using hk) hv]
  rw [ite_eq_right (by simp only [ite_true]; omega)]

theorem direction_replace_self (f : List Bool) (v h i : ℕ)
    (hW : 0 < width f) (hk : 2 * key h i + 1 < cells f) (hv : v < 2 ^ width f) :
    direction (packet (replace f (2 * key h i + 1) v) h i) = v := by
  unfold direction
  rw [read_replace true f (2 * key h i + 1) v h i hW (by simpa only [ite_true] using hk) hv]
  simp only [ite_true, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Algebra.BalancedMetadataTable
