/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimeBinary

/-! # Native polynomial-time arithmetic with binary natural outputs

Unlike unary output certificates, these permit exponentially large values.
All arithmetic below is supplied by Complexitylib2's native machine calculus.
-/

@[expose] public section

namespace LeanCanny
open Turing.MultiTapeTM

abbrev BinaryFn (f : List Bool → ℕ) : Prop :=
  ComputableTidilyInPolyTime f encBits encNat

theorem BinaryFn.bits_mem_FP {f : List Bool → ℕ} (hf : BinaryFn f) :
    (fun z => BinaryNatCode.encode (f z)) ∈ FP := natBits_computable.comp hf

theorem BinaryFn.fromBits {f : List Bool → List Bool} (hf : f ∈ FP) :
    BinaryFn (fun z => Nat.fromBitsLE (f z)) := fromBitsLE_computable.comp hf

theorem BinaryFn.of_bits {f : List Bool → ℕ}
    (hf : (fun z => BinaryNatCode.encode (f z)) ∈ FP) : BinaryFn f := by
  have h := BinaryFn.fromBits hf
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using h

theorem BinaryFn.const (n : ℕ) : BinaryFn (fun _ => n) := ComputableTidilyInPolyTime.const n

theorem BinaryFn.add {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun z => f z + g z) := ComputableTidilyInPolyTime.binary_add' hf hg

theorem BinaryFn.mul {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun z => f z * g z) := ComputableTidilyInPolyTime.binary_mul' hf hg

theorem BinaryFn.size {f : List Bool → ℕ} (hf : BinaryFn f) : BinaryFn (fun z => (f z).size) :=
  BinaryFn.of_bits (mem_FP_of_eq (LeanCanny.bits_mem_FP (UnaryFn.length hf.bits_mem_FP)) fun z =>
    congrArg Nat.bits (Nat.size_eq_bits_len (f z)))

end LeanCanny
