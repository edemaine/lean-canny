/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerEncoding
public import LeanCanny.Encoding.BinaryNatFP
public import Complexitylib.Classes.P.NatCodes

/-!
# Polynomial-time binary query operations for matrix powering

The parent height is decremented and the exponent is halved directly in binary.
Both child writers are total FP functions on strings and agree exactly with the
typed queries on encoded inputs. The initial height is written from the exponent
word's length; the exponent's magnitude is never expanded to unary.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.QueryBits
open Complexity
open LeanCanny.Encoding

def height (bits : List Bool) : List Bool := pairFst bits
def exponent (bits : List Bool) : List Bool := pairFst (pairSnd bits)
def row (bits : List Bool) : List Bool := pairFst (pairSnd (pairSnd bits))
def col (bits : List Bool) : List Bool := pairSnd (pairSnd (pairSnd bits))

def build (h e i j : List Bool) : List Bool := pair h (pair e (pair i j))

theorem height_mem_FP : height ∈ FP := pairFst_mem_FP
theorem exponent_mem_FP : exponent ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem row_mem_FP : row ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem col_mem_FP : col ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

theorem build_mem_FP {h e i j : List Bool → List Bool}
    (hh : h ∈ FP) (he : e ∈ FP) (hi : i ∈ FP) (hj : j ∈ FP) :
    (fun bits => build (h bits) (e bits) (i bits) (j bits)) ∈ FP :=
  mem_FP_pair hh (mem_FP_pair he (mem_FP_pair hi hj))

/-- Input: `pair parentQuery binaryPivot`. -/
def childLeft (packet : List Bool) : List Bool :=
  let q := pairFst packet
  build (BinaryNat.pred (height q)) (BinaryNat.half (exponent q)) (row q) (pairSnd packet)

def childRight (packet : List Bool) : List Bool :=
  let q := pairFst packet
  build (BinaryNat.pred (height q)) (BinaryNat.upperHalf (exponent q)) (pairSnd packet) (col q)

theorem childLeft_mem_FP : childLeft ∈ FP := by
  have hh := mem_FP_comp (mem_FP_comp pairFst_mem_FP height_mem_FP) BinaryNat.pred_mem_FP
  have he := mem_FP_comp (mem_FP_comp pairFst_mem_FP exponent_mem_FP) BinaryNat.half_mem_FP
  have hi := mem_FP_comp pairFst_mem_FP row_mem_FP
  have h := build_mem_FP hh he hi pairSnd_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem childRight_mem_FP : childRight ∈ FP := by
  have hh := mem_FP_comp (mem_FP_comp pairFst_mem_FP height_mem_FP) BinaryNat.pred_mem_FP
  have he := mem_FP_comp (mem_FP_comp pairFst_mem_FP exponent_mem_FP) BinaryNat.upperHalf_mem_FP
  have hj := mem_FP_comp pairFst_mem_FP col_mem_FP
  have h := build_mem_FP hh he pairSnd_mem_FP hj
  exact mem_FP_of_eq h (fun _ => rfl)

theorem childLeft_queryBits {n : ℕ} (q : Query n) (k : Fin n) :
    childLeft (pair (queryBits q) (BinaryNatCode.encode k.val)) = queryBits (q.left k) := by
  simp only [childLeft, queryBits, pairFst_pair, pairSnd_pair, height, exponent, row,
    BinaryNat.pred_eq_bits, BinaryNat.half_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Query.left, build]

theorem childRight_queryBits {n : ℕ} (q : Query n) (k : Fin n) :
    childRight (pair (queryBits q) (BinaryNatCode.encode k.val)) = queryBits (q.right k) := by
  simp only [childRight, queryBits, pairFst_pair, pairSnd_pair, height, exponent, col,
    BinaryNat.pred_eq_bits, BinaryNat.upperHalf_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Query.right, build]

/-- Input: `pair binaryExponent (pair binaryRow binaryColumn)`. -/
def initial (packet : List Bool) : List Bool :=
  pair (BinaryNatCode.encode (pairFst packet).length) packet

theorem initial_mem_FP : initial ∈ FP := by
  have hh := bits_mem_FP (UnaryFn.length pairFst_mem_FP)
  exact mem_FP_pair hh id_mem_FP

theorem initial_queryBits {n : ℕ} (e : ℕ) (i j : Fin n) :
    initial (pair (BinaryNatCode.encode e)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        queryBits ⟨e.size, e, i, j⟩ := by
  simp only [initial, pairFst_pair, BinaryNatCode.length_encode, queryBits]

end LeanCanny.Algebra.MatrixPower.QueryBits
