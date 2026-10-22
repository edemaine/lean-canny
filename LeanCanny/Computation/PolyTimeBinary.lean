/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimeFunctions
public import LeanCanny.Encoding.BinaryNatCode
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! # Native polynomial-time certificates for binary natural codecs -/

@[expose] public section

namespace LeanCanny

open Turing.MultiTapeTM

theorem fromBitsLE_eq_ofBits (w : List Bool) : Nat.fromBitsLE w = ofBits w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Nat.fromBitsLE_cons, ofBits, List.foldr_cons, ← ofBits, ← ih, Nat.bit_val]
    cases b <;> simp [Nat.add_comm]

theorem fromBitsLE_computable :
    ComputableTidilyInPolyTime Nat.fromBitsLE encBits encNat :=
  ComputableTidilyInPolyTime.bitsToNat.of_enc_eq fun w =>
    congrArg encNat (fromBitsLE_eq_ofBits w)

theorem natBits_computable : ComputableTidilyInPolyTime Nat.bits encNat encBits :=
  .of_eq fun _ => rfl

theorem bits_mem_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun z => (n z).bits) ∈ FP :=
  (ComputableTidilyInPolyTime.unary_to_binary.comp hn).encoded

theorem bits_length_mem_FP : (fun z : List Bool => z.length.bits) ∈ FP :=
  bits_mem_FP (UnaryFn.length id_mem_FP)

theorem UnaryFn.fromBitsLE_min {s : List Bool → List Bool} {cap : List Bool → ℕ}
    (hs : s ∈ FP) (hc : UnaryFn cap) :
    UnaryFn (fun z => Min.min (Nat.fromBitsLE (s z)) (cap z)) := by
  have h := ComputableTidilyInPolyTime.bitsBoundedBinaryValueWithInput hc
    (mem_FP_comp hs reverse_mem_FP)
  refine UnaryFn.of_eq h fun z => ?_
  rw [Cslib.BitString.boundedBinaryValue_eq, ← ofBits_reverse, Function.comp_apply,
    List.reverse_reverse, ← fromBitsLE_eq_ofBits, Nat.min_comm]

theorem UnaryFn.fromBitsLE_of_le {s : List Bool → List Bool} {cap : List Bool → ℕ}
    (hs : s ∈ FP) (hc : UnaryFn cap) (h : ∀ z, Nat.fromBitsLE (s z) ≤ cap z) :
    UnaryFn (fun z => Nat.fromBitsLE (s z)) :=
  (UnaryFn.fromBitsLE_min hs hc).of_eq fun z => min_eq_left (h z)

end LeanCanny
