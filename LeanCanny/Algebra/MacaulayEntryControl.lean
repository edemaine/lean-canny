/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomialFP

/-! # Polynomial-time controls for padded Macaulay entries

A query is `pair (pair context modulusMinusOne) (pair row column)`.
Degrees, arity and block width have polynomially bounded unary writers. Binary
exponents are clipped only for the total-degree test. A bounded search selects
the first divisible coordinate, and fixed-width subtraction writes the source
coefficient query without enumerating monomials.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayBits

open LeanCanny.Encoding
open scoped BigOperators

theorem fromBits_encode (i : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits i

structure Layout where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  degree : List Bool → ℕ → ℕ

structure Layout.PolyTime (L : Layout) : Prop where
  arity : UnaryFn L.arity
  width : UnaryFn L.width
  degree : UnaryFn (fun q => L.degree (pairFst q) (pairSnd q).length)

def context (p : List Bool) : List Bool := pairFst (pairFst p)
def row (p : List Bool) : List Bool := pairFst (pairSnd p)
def col (p : List Bool) : List Bool := pairSnd (pairSnd p)

theorem context_mem_FP : context ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem row_mem_FP : row ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem col_mem_FP : col ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

def Layout.level (L : Layout) (c : List Bool) : ℕ :=
  (∑ i ∈ Finset.range (L.arity c), (L.degree c i - 1)) + 1

theorem Layout.level_unary {L : Layout} (h : L.PolyTime) : UnaryFn L.level := by
  exact ((h.arity.sum (h.degree.sub (UnaryFn.const 1))).add (UnaryFn.const 1)).of_eq
    (fun c => by simp only [Layout.level, pairFst_pair, pairSnd_pair, List.length_replicate])

def rowAt (L : Layout) (p : List Bool) (i : ℕ) : ℕ :=
  FixedWidthQuery.entry (L.arity ∘ context) (L.width ∘ context) row p i

def colAt (L : Layout) (p : List Bool) (i : ℕ) : ℕ :=
  FixedWidthQuery.entry (L.arity ∘ context) (L.width ∘ context) col p i

def rowRead (L : Layout) : List Bool → List Bool :=
  FixedWidthQuery.read (L.arity ∘ context) (L.width ∘ context) row

def colRead (L : Layout) : List Bool → List Bool :=
  FixedWidthQuery.read (L.arity ∘ context) (L.width ∘ context) col

theorem rowRead_mem_FP {L : Layout} (h : L.PolyTime) : rowRead L ∈ FP :=
  FixedWidthQuery.read_mem_FP (h.arity.comp context_mem_FP) (h.width.comp context_mem_FP) row_mem_FP

theorem colRead_mem_FP {L : Layout} (h : L.PolyTime) : colRead L ∈ FP :=
  FixedWidthQuery.read_mem_FP (h.arity.comp context_mem_FP) (h.width.comp context_mem_FP) col_mem_FP

def loopQuery (q : List Bool) : List Bool := pair (pairFst q) (BinaryNatCode.encode (pairSnd q).length)

theorem loopQuery_mem_FP : loopQuery ∈ FP := mem_FP_pair pairFst_mem_FP (bits_mem_FP UnaryFn.index)

def degreeLoop (L : Layout) (q : List Bool) : ℕ := L.degree (context (pairFst q)) (pairSnd q).length

theorem degreeLoop_unary {L : Layout} (h : L.PolyTime) : UnaryFn (degreeLoop L) := by
  refine (h.degree.comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP context_mem_FP) pairSnd_mem_FP)).of_eq ?_
  intro q
  simp only [degreeLoop, Function.comp_apply, pairFst_pair, pairSnd_pair]

def rowTotal (L : Layout) (p : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (L.arity (context p)), min (rowAt L p i) (L.level (context p) + 1)

theorem rowTotal_unary {L : Layout} (h : L.PolyTime) : UnaryFn (rowTotal L) := by
  have hr := mem_FP_comp loopQuery_mem_FP (rowRead_mem_FP h)
  have hc := (((Layout.level_unary h).comp context_mem_FP).add (UnaryFn.const 1)).comp pairFst_mem_FP
  have hs := (h.arity.comp context_mem_FP).sum (UnaryFn.fromBitsLE_min hr hc)
  refine hs.of_eq (fun p => ?_)
  simp only [loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate,
    rowRead, FixedWidthQuery.read_packet, fromBits_encode, rowTotal, rowAt]

def pivot (L : Layout) (p : List Bool) : ℕ :=
  (List.range (L.arity (context p))).findIdx (fun i => decide (L.degree (context p) i ≤ rowAt L p i))

theorem pivot_unary {L : Layout} (h : L.PolyTime) : UnaryFn (pivot L) := by
  have hr := mem_FP_comp loopQuery_mem_FP (rowRead_mem_FP h)
  have ht := BinaryNat.le_fppred (bits_mem_FP (degreeLoop_unary h)) hr
  have hf := (h.arity.comp context_mem_FP).find ht
  refine hf.of_eq (fun p => ?_)
  simp only [pivot, degreeLoop, loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate, rowRead, FixedWidthQuery.read_packet, fromBits_encode, Nat.fromBitsLE_bits, rowAt]
  rfl

def remainderAt (L : Layout) (p : List Bool) (i : ℕ) : ℕ :=
  rowAt L p i - if i = pivot L p then L.degree (context p) (pivot L p) else 0

def remainderRead (L : Layout) (q : List Bool) : List Bool :=
  BinaryNat.sub (pair (rowRead L q)
    (if Nat.fromBitsLE (pairSnd q) = pivot L (pairFst q) then
      BinaryNatCode.encode (L.degree (context (pairFst q)) (pivot L (pairFst q))) else []))

theorem remainderRead_mem_FP {L : Layout} (h : L.PolyTime) : remainderRead L ∈ FP := by
  have hp := pivot_unary h
  have hi := bits_mem_FP (hp.comp pairFst_mem_FP)
  have he : FPPred (fun q => Nat.fromBitsLE (pairSnd q) = pivot L (pairFst q)) :=
    ((BinaryNat.le_fppred pairSnd_mem_FP hi).and
    (BinaryNat.le_fppred hi pairSnd_mem_FP)).of_iff (fun q => by
      simp only [Nat.fromBitsLE_bits]; omega)
  have hd : UnaryFn (fun q => L.degree (context (pairFst q)) (pivot L (pairFst q))) := by
    refine (h.degree.comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP context_mem_FP)
      (hp.comp pairFst_mem_FP).mem_FP)).of_eq ?_
    intro q
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]
  have hb := he.ite_mem_FP (bits_mem_FP hd) (constFn_mem_FP [])
  exact mem_FP_comp (mem_FP_pair (rowRead_mem_FP h) hb) BinaryNat.sub_mem_FP

theorem remainderRead_packet (L : Layout) (p : List Bool) (i : ℕ) :
    remainderRead L (pair p (BinaryNatCode.encode i)) = BinaryNatCode.encode (remainderAt L p i) := by
  simp only [remainderRead, rowRead, FixedWidthQuery.read_packet, pairFst_pair, pairSnd_pair,
    BinaryNat.sub_pair, fromBits_encode, remainderAt, rowAt]
  split_ifs
  · rw [fromBits_encode]
    rfl
  · rfl

end LeanCanny.Algebra.MacaulayBits
