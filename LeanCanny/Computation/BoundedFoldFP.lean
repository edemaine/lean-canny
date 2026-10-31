/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Computation.PolyTimeIteration

/-! # Polynomial-time bounded folds with unary counts

A polynomial number of FP updates remains FP when every accumulator prefix
has a unary-readable size bound. The update receives the same raw packet as
the space fold, allowing modular products and growing bounded tables to use
one implementation with either native time or space certificates.
-/

@[expose] public section
namespace LeanCanny.Computation.BoundedFold
open LeanCanny.Encoding
set_option backward.isDefEq.respectTransparency false

def advance (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (BinaryNat.succ (counter p)) (f p))

attribute [local irreducible] BinaryNat.succ

theorem advance_FP (f : List Bool → List Bool) (hf : f ∈ FP) : advance f ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (mem_FP_comp (f := counter) (g := BinaryNat.succ) counter_mem_FP BinaryNat.succ_mem_FP) hf)

theorem iterate_advance (f seed : List Bool → List Bool) (c : List Bool) (n : ℕ) :
    (advance f)^[n] (init seed c) = packet c n (fold f seed c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [advance, context_packet, counter_packet, BinaryNat.succ_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl

theorem evaluator_FP (f seed : List Bool → List Bool) (count B : List Bool → ℕ)
    (hf : f ∈ FP) (hs : seed ∈ FP) (hc : UnaryFn count) (hB : UnaryFn B)
    (hstate : ∀ c n, n ≤ count c → (fold f seed c n).length ≤ B c) :
    (fun c => fold f seed c (count c)) ∈ FP := by
  let ruler := fun c => List.replicate (count c) true
  let width := fun c => List.replicate (2 * c.length + 2 * count c + B c + 4) false
  have HR : ruler ∈ FP := hc.replicate_mem_FP true
  have HW : width ∈ FP :=
    (((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul hc)).add hB).add
      (UnaryFn.const 4)).replicate_mem_FP false
  have E := iterate_mem_FP (advance_FP f hf) (init_mem_FP hs) HR HW (by
    intro c n hn
    have HN : n ≤ count c := by simpa only [ruler, List.length_replicate] using hn
    rw [iterate_advance]
    have HI := (Nat.size_le_self n).trans HN
    have HS := hstate c n HN
    simp only [packet, pair_length, BinaryNatCode.length_encode, width, List.length_replicate]
    omega)
  refine mem_FP_of_eq (mem_FP_comp E accumulator_mem_FP) (fun c => ?_)
  simp only [ruler, List.length_replicate, Function.comp_apply, iterate_advance, accumulator_packet]

end LeanCanny.Computation.BoundedFold
