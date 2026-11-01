/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.RecursiveFoldController
public import LeanCanny.Encoding.FixedWidthNatVectorSpace
/-! # Native bounded reply tables without a child evaluator

A resumable fold writes one fixed-width bit at a time. Only actual table
coordinates need reply equations. The accumulator length is bounded for
every reply function, including malformed replies.
-/
@[expose] public section
namespace LeanCanny.Computation.FixedWidthVectorPass
open LeanCanny.Encoding Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

def entryQuery (A W : List Bool → ℕ) (p : List Bool) :=
  pair (pairFst p) (BinaryNatCode.encode (min (Nat.fromBitsLE (pairSnd p)) (A (pairFst p) * W (pairFst p)) / W (pairFst p)))

def program (A W : List Bool → ℕ) (task : List Bool → List Bool) : RecursiveFold.Program where
  count q := A q * W q
  seed _ := []
  entryTask := task ∘ entryQuery A W
  finish := FixedWidthNatVector.writeFinish A W

theorem finish_FP (A W : List Bool → ℕ) (ha : UnaryFn A) (hw : UnaryFn W) :
    FixedWidthNatVector.writeFinish A W ∈ FP := by
  have hi := FixedWidthNatVector.writeIndex_unary ha hw
  have hoffset := (hi.mod hw.lift).lift
  have hacc : (fun z => BoundedFold.accumulator (pairFst z)) ∈ FP := mem_FP_comp (f := pairFst) (g := BoundedFold.accumulator) pairFst_mem_FP BoundedFold.accumulator_mem_FP
  exact appendFn_mem_FP hacc (getBit_mem_FP pairSnd_mem_FP hoffset)

theorem certificates (A W : List Bool → ℕ) (ha : UnaryFn A) (hw : UnaryFn W)
    (task : List Bool → List Bool) (ht : task ∈ FP) :
    (program A W task).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) := by
  have hi : UnaryFn (fun p => min (Nat.fromBitsLE (pairSnd p)) (A (pairFst p) * W (pairFst p))) :=
    UnaryFn.fromBitsLE_min pairSnd_mem_FP ((ha.mul hw).comp pairFst_mem_FP)
  have hquery : entryQuery A W ∈ FP := mem_FP_pair pairFst_mem_FP (bits_mem_FP (hi.div (hw.comp pairFst_mem_FP)))
  exact RecursiveFold.Program.certificates _ (BinaryFn.ofUnary (ha.mul hw)) (constFn_mem_FP [])
    (mem_FP_comp (f := entryQuery A W) (g := task) hquery ht) (finish_FP A W ha hw)

theorem update_eq (A W : List Bool → ℕ) (task answer : List Bool → List Bool) :
    (program A W task).update answer = FixedWidthNatVector.writeStep A W (answer ∘ task) := by
  funext p
  simp only [RecursiveFold.Program.update, program, BoundedFold.update, BoundedFold.query, Function.comp_apply,
    entryQuery, pairFst_pair, pairSnd_pair, FixedWidthNatVector.writeStep, FixedWidthNatVector.writeQuery, FixedWidthNatVector.writeIndex]

theorem fold_length (A W : List Bool → ℕ) (read : List Bool → List Bool) (q : List Bool) (k : ℕ) :
    (BoundedFold.fold (FixedWidthNatVector.writeStep A W read) (fun _ => []) q k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [BoundedFold.fold, FixedWidthNatVector.writeStep, FixedWidthNatVector.writeFinish,
      pairFst_pair, BoundedFold.accumulator_packet, List.length_append, List.length_singleton, ih]

theorem partial_length (A W : List Bool → ℕ) (task answer : List Bool → List Bool) (q : List Bool) (k : ℕ) :
    ((program A W task).partialValue answer q k).length = k := by
  unfold RecursiveFold.Program.partialValue
  rw [update_eq]
  exact fold_length A W (answer ∘ task) q k

theorem write_fold_current (A W : List Bool → ℕ) (e : ℕ → ℕ) (read : List Bool → List Bool)
    (q : List Bool) (he : ∀ i < A q, read (pair q (BinaryNatCode.encode i)) = BinaryNatCode.encode (e i))
    (k : ℕ) (hk : k ≤ A q * W q) :
    BoundedFold.fold (FixedWidthNatVector.writeStep A W read) (fun _ => []) q k =
      (List.range k).map (fun j => (e (j / W q)).testBit (j % W q)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have HK : k < A q * W q := by omega
    have HW : 0 < W q := by
      by_contra hn
      have H : W q = 0 := by omega
      rw [H, Nat.mul_zero] at HK
      exact Nat.not_lt_zero _ HK
    have HI : k / W q < A q := (Nat.div_lt_iff_lt_mul HW).2 HK
    rw [BoundedFold.fold, ih (by omega)]
    simp only [FixedWidthNatVector.writeStep, FixedWidthNatVector.writeFinish, FixedWidthNatVector.writeQuery,
      FixedWidthNatVector.writeIndex, pairFst_pair, pairSnd_pair, BoundedFold.counter_packet,
      BoundedFold.accumulator_packet, BoundedFold.context_packet,
      show Nat.fromBitsLE (BinaryNatCode.encode k) = k from Nat.fromBitsLE_bits k,
      min_eq_left HK.le]
    rw [he _ HI, ← BinaryNat.fromBitsLE_testBit]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, List.range_succ, List.map_append, List.map_singleton]

theorem value_at (A W : List Bool → ℕ) (task answer : List Bool → List Bool) (e : ℕ → ℕ)
    (q : List Bool) (he : ∀ i < A q, answer (task (pair q (BinaryNatCode.encode i))) = BinaryNatCode.encode (e i)) :
    (program A W task).value answer q = FixedWidthNatVector.encode (A q) (W q) e := by
  unfold RecursiveFold.Program.value RecursiveFold.Program.partialValue
  rw [update_eq]
  change BoundedFold.fold (FixedWidthNatVector.writeStep A W (answer ∘ task)) (fun _ => []) q (A q * W q) = _
  rw [write_fold_current A W e (answer ∘ task) q he _ le_rfl]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, FixedWidthNatVector.length_encode]
  · intro k hk hk'
    simp only [List.getElem_map, List.getElem_range, FixedWidthNatVector.encode, List.getElem_ofFn]

theorem requests_coordinate (A W : List Bool → ℕ) (task answer : List Bool → List Bool) (q c : List Bool)
    (hc : (program A W task).controller.Requests answer (program A W task).count q c) :
    ∃ i < A q, c = task (pair q (BinaryNatCode.encode i)) := by
  obtain ⟨k, hk, rfl⟩ := ((program A W task).requests_iff answer q c).mp hc
  change k < A q * W q at hk
  have HW : 0 < W q := by
    by_contra hn
    have H : W q = 0 := by omega
    rw [H, Nat.mul_zero] at hk
    exact Nat.not_lt_zero _ hk
  refine ⟨k / W q, (Nat.div_lt_iff_lt_mul HW).2 hk, ?_⟩
  simp only [RecursiveFold.Program.child, program, Function.comp_apply, entryQuery,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, min_eq_left hk.le]

end LeanCanny.Computation.FixedWidthVectorPass
