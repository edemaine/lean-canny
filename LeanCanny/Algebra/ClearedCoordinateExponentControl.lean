/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ClearedCoordinateCoefficients
public import LeanCanny.Computation.PolyTimeBinaryRange

/-! # Native free-exponent masks for frozen-coordinate substitution

The mask compares only the free spatial coordinates. Both exponent ranks
stay binary; bounded fixed-width reads and a unary spatial loop derive its
FP program directly from the original query words.
-/

@[expose] public section
namespace LeanCanny.Algebra.ClearedCoordinateExponentBits
open LeanCanny.Encoding
set_option backward.isDefEq.respectTransparency false

structure Layout where
  arity : List Bool → ℕ
  free : List Bool → ℕ
  offset : List Bool → ℕ
  sourceWidth : List Bool → ℕ
  targetWidth : List Bool → ℕ
  sourceWord : List Bool → List Bool
  targetWord : List Bool → List Bool

structure Controls (L : Layout) : Prop where
  arity : UnaryFn L.arity
  free : UnaryFn L.free
  offset : UnaryFn L.offset
  sourceWidth : UnaryFn L.sourceWidth
  targetWidth : UnaryFn L.targetWidth
  sourceWord : L.sourceWord ∈ FP
  targetWord : L.targetWord ∈ FP

def shiftedQuery (offset : List Bool → ℕ) (q : List Bool) : List Bool :=
  pair (pairFst q) (BinaryNatCode.encode (offset (pairFst q) + (pairSnd q).length))

theorem shiftedQuery_FP (offset : List Bool → ℕ) (h : UnaryFn offset) : shiftedQuery offset ∈ FP := by
  have HO : BinaryFn (fun q => offset (pairFst q)) := BinaryFn.ofUnary (h.comp pairFst_mem_FP)
  exact mem_FP_pair pairFst_mem_FP (HO.add (BinaryFn.ofUnary UnaryFn.index)).bits_mem_FP

def shiftedRead (A W offset : List Bool → ℕ) (word : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthQuery.read A W word ∘ shiftedQuery offset

theorem shiftedRead_FP (A W offset : List Bool → ℕ) (word : List Bool → List Bool)
    (hA : UnaryFn A) (hW : UnaryFn W) (ho : UnaryFn offset) (hw : word ∈ FP) : shiftedRead A W offset word ∈ FP :=
  mem_FP_comp (shiftedQuery_FP offset ho) (FixedWidthQuery.read_mem_FP hA hW hw)

theorem shiftedRead_packet (A W offset : List Bool → ℕ) (word : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    shiftedRead A W offset word (pair c (List.replicate i true)) =
      BinaryNatCode.encode (FixedWidthQuery.entry A W word c (offset c + i)) := by
  simp only [shiftedRead, Function.comp_apply, shiftedQuery, pairFst_pair, pairSnd_pair, List.length_replicate]
  exact FixedWidthQuery.read_packet A W word c (offset c + i)

def mask (L : Layout) (c : List Bool) : Prop :=
  ∀ i < L.free c, FixedWidthQuery.entry L.arity L.sourceWidth L.sourceWord c (L.offset c + i) =
    FixedWidthQuery.entry L.free L.targetWidth L.targetWord c i

instance (L : Layout) (c : List Bool) : Decidable (mask L c) :=
  inferInstanceAs (Decidable (∀ i < L.free c,
    FixedWidthQuery.entry L.arity L.sourceWidth L.sourceWord c (L.offset c + i) =
      FixedWidthQuery.entry L.free L.targetWidth L.targetWord c i))

theorem mask_fppred (L : Layout) (h : Controls L) : FPPred (mask L) := by
  have HS := shiftedRead_FP L.arity L.sourceWidth L.offset L.sourceWord h.arity h.sourceWidth h.offset h.sourceWord
  have HT := shiftedRead_FP L.free L.targetWidth (fun _ => 0) L.targetWord h.free h.targetWidth (UnaryFn.const 0) h.targetWord
  apply ((BinaryNat.eq_fppred HS HT).forall_lt h.free).of_iff
  intro c
  simp only [shiftedRead_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.zero_add, mask]

theorem entry_encoded (A W : List Bool → ℕ) (word : List Bool → List Bool) (c : List Bool)
    (k i : ℕ) (hi : i < A c) (hw : word c = BinaryNatCode.encode k) :
    FixedWidthQuery.entry A W word c i = FixedWidthPolynomial.entry (W c) k i := by
  rw [FixedWidthQuery.entry, ite_eq_left hi]
  unfold FixedWidthQuery.coordinate
  rw [hw]
  rfl

theorem mask_eq (L : Layout) (c : List Bool) (hfit : L.offset c + L.free c ≤ L.arity c)
    (r : Fin (FixedWidthPolynomial.count (L.arity c) (L.sourceWidth c))) (k : ℕ)
    (hs : L.sourceWord c = BinaryNatCode.encode r.val) (ht : L.targetWord c = BinaryNatCode.encode k) :
    mask L c ↔ ClearedCoordinateBlock.freeExponent (L.offset c) (L.free c)
      (FixedWidthPolynomial.vector _ _ r) = RationalSubstitution.Indexed.exponentVector (L.free c)
        (FixedWidthPolynomial.entry (L.targetWidth c) k) := by
  have HS (j : Fin (L.free c)) :
      FixedWidthQuery.entry L.arity L.sourceWidth L.sourceWord c (L.offset c + j.val) =
        FixedWidthPolynomial.vector _ _ r ⟨L.offset c + j.val, by omega⟩ := by
    rw [entry_encoded L.arity L.sourceWidth L.sourceWord c r.val _ (by omega) hs,
      FixedWidthPolynomial.entry_eq_digit, FixedWidthPolynomial.vector_apply]
  have HT (j : Fin (L.free c)) : FixedWidthQuery.entry L.free L.targetWidth L.targetWord c j.val =
      (RationalSubstitution.Indexed.exponentVector (L.free c) (FixedWidthPolynomial.entry (L.targetWidth c) k)) j :=
    entry_encoded L.free L.targetWidth L.targetWord c k j.val j.isLt ht
  constructor
  · intro h
    apply Finsupp.ext
    intro j
    rw [ClearedCoordinateBlock.freeExponent_apply _ hfit]
    have H := h j.val j.isLt
    rw [HS j, HT j] at H
    exact H
  · intro h i hi
    let j : Fin (L.free c) := ⟨i, hi⟩
    have H := congrArg (fun e : Fin (L.free c) →₀ ℕ => e j) h
    rw [ClearedCoordinateBlock.freeExponent_apply _ hfit] at H
    change FixedWidthQuery.entry L.arity L.sourceWidth L.sourceWord c (L.offset c + j.val) =
      FixedWidthQuery.entry L.free L.targetWidth L.targetWord c j.val
    rw [HS j, HT j]
    exact H

end LeanCanny.Algebra.ClearedCoordinateExponentBits
