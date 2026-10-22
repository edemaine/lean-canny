/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FixedWidthQuery
public import LeanCanny.Computation.BoundedFoldSpace

/-! # Writing fixed-width tables from polynomial-space coordinate readers

Only the number and width of coordinates must be unary FP. A coordinate
computation may take arbitrary time in polynomial space. The native fold
retains at most the polynomial-size output prefix and one child computation.
Oversized values are truncated, exactly as in the mathematical vector encoder.
-/

@[expose] public section

namespace LeanCanny.Encoding.FixedWidthNatVector
open LeanCanny.Computation

def writeIndex (A W : List Bool → ℕ) (p : List Bool) : ℕ :=
  min (Nat.fromBitsLE (BoundedFold.counter p)) (A (pairFst p) * W (pairFst p))

def writeQuery (A W : List Bool → ℕ) (p : List Bool) : List Bool :=
  pair (pairFst p) (BinaryNatCode.encode (writeIndex A W p / W (pairFst p)))

def writeFinish (A W : List Bool → ℕ) (p : List Bool) : List Bool :=
  BoundedFold.accumulator (pairFst p) ++
    [(pairSnd p)[writeIndex A W (pairFst p) % W (pairFst (pairFst p))]?.getD false]

def writeStep (A W : List Bool → ℕ) (read : List Bool → List Bool) (p : List Bool) : List Bool :=
  writeFinish A W (pair p (read (writeQuery A W p)))

attribute [local irreducible] BinaryNat.normalize

theorem writeIndex_unary {A W : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W) : UnaryFn (writeIndex A W) :=
  UnaryFn.fromBitsLE_min BoundedFold.counter_mem_FP (hA.mul hW).lift

theorem writeStepEvaluator {A W : List Bool → ℕ} {read : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (R : SpaceFunction read) : SpaceFunction (writeStep A W read) := by
  have hi := writeIndex_unary hA hW
  have hquery : writeQuery A W ∈ FP := mem_FP_pair pairFst_mem_FP (bits_mem_FP (hi.div hW.lift))
  have hoffset := (hi.mod hW.lift).lift
  have hacc := mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP
  have hfinish : writeFinish A W ∈ FP := appendFn_mem_FP hacc (getBit_mem_FP pairSnd_mem_FP hoffset)
  have E := ((R.precompose (writeQuery A W) hquery).withInput).postcompose (writeFinish A W) hfinish
  exact E.congr (funext fun p => by simp only [writeStep, Function.comp_apply])

theorem write_fold (A W : List Bool → ℕ) (e : List Bool → ℕ → ℕ) (read : List Bool → List Bool)
    (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = BinaryNatCode.encode (e c i))
    (c : List Bool) (k : ℕ) (hk : k ≤ A c * W c) :
    BoundedFold.fold (writeStep A W read) (fun _ => []) c k =
      (List.range k).map (fun j => (e c (j / W c)).testBit (j % W c)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BoundedFold.fold, ih (by omega)]
    simp only [writeStep, writeFinish, writeQuery, writeIndex, pairFst_pair, pairSnd_pair,
      BoundedFold.counter_packet, BoundedFold.accumulator_packet, BoundedFold.context_packet,
      show Nat.fromBitsLE (BinaryNatCode.encode k) = k from Nat.fromBitsLE_bits k,
      Nat.min_eq_left (show k ≤ A c * W c by omega)]
    rw [he, ← BinaryNat.fromBitsLE_testBit]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, List.range_succ, List.map_append, List.map_singleton]

theorem encodeEvaluator (A W : List Bool → ℕ) (e : List Bool → ℕ → ℕ)
    (hA : UnaryFn A) (hW : UnaryFn W) (read : List Bool → List Bool) (R : SpaceFunction read)
    (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = BinaryNatCode.encode (e c i)) :
    SpaceFunction (fun c => encode (A c) (W c) (e c)) := by
  obtain ⟨s, hs⟩ := output_length_poly_of_mem_FP (hA.mul hW).mem_FP
  have hbound (c : List Bool) : A c * W c ≤ s.eval c.length := by
    simpa only [List.length_replicate] using hs c
  have E := BoundedFold.evaluator (writeStepEvaluator hA hW R)
    (fun c => BinaryNatCode.encode (A c * W c)) (fun _ => []) (bits_mem_FP (hA.mul hW)) (constFn_mem_FP []) s
    (fun c k hk => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits] at hk
      rw [write_fold A W e read he c k hk, List.length_map, List.length_range]
      exact hk.trans (hbound c))
  refine E.congr (funext fun c => ?_)
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, write_fold A W e read he c _ (Nat.le_refl _)]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, length_encode]
  · intro k hk hk'
    simp only [List.getElem_map, List.getElem_range, encode, List.getElem_ofFn]

end LeanCanny.Encoding.FixedWidthNatVector
