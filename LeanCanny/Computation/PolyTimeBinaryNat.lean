/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimeBinary
public import Complexity.Tactic.PolyTime.Init

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

theorem BinaryFn.of_eq {f g : List Bool → ℕ} (hf : BinaryFn f)
    (h : ∀ z, f z = g z) : BinaryFn g := by
  simpa only [funext h] using hf

theorem BinaryFn.ofUnary {f : List Bool → ℕ} (hf : UnaryFn f) : BinaryFn f :=
  ComputableTidilyInPolyTime.unary_to_binary.comp hf

theorem BinaryFn.add {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun z => f z + g z) := ComputableTidilyInPolyTime.binary_add' hf hg

theorem BinaryFn.mul {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun z => f z * g z) := ComputableTidilyInPolyTime.binary_mul' hf hg

theorem BinaryFn.sub {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun z => f z - g z) := ComputableTidilyInPolyTime.binary_sub' hf hg

theorem BinaryFn.le {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    FPPred (fun z => f z ≤ g z) :=
  .of_computable (ComputableTidilyInPolyTime.binary_le' hf hg)
    fun _ => decide_eq_true_iff.symm

theorem BinaryFn.lt {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    FPPred (fun z => f z < g z) :=
  .of_computable (ComputableTidilyInPolyTime.binary_lt' hf hg)
    fun _ => decide_eq_true_iff.symm

theorem BinaryFn.eq {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    FPPred (fun z => f z = g z) :=
  .of_computable (ComputableTidilyInPolyTime.decide_eq encNat |>.comp (hf.prod hg))
    fun _ => decide_eq_true_iff.symm

theorem BinaryFn.ite {p : List Bool → Prop} [DecidablePred p] {f g : List Bool → ℕ}
    (hp : FPPred p) (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun z => if p z then f z else g z) := hp.computable.ite_decide hf hg

theorem BinaryFn.powUnary {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : UnaryFn g) :
    BinaryFn (fun z => f z ^ g z) := ComputableTidilyInPolyTime.binary_pow' hf hg

theorem BinaryFn.size {f : List Bool → ℕ} (hf : BinaryFn f) : BinaryFn (fun z => (f z).size) :=
  BinaryFn.of_bits (mem_FP_of_eq (LeanCanny.bits_mem_FP (UnaryFn.length hf.bits_mem_FP)) fun z =>
    congrArg Nat.bits (Nat.size_eq_bits_len (f z)))

-- These native certificates also register their existing `fun_prop` rules.
attribute [program_certificate] fromBitsLE_computable natBits_computable
attribute [program_certificate] ComputableTidilyInPolyTime.binary_sub
  ComputableTidilyInPolyTime.binary_sub' ComputableTidilyInPolyTime.binary_le
  ComputableTidilyInPolyTime.binary_le' ComputableTidilyInPolyTime.binary_lt
  ComputableTidilyInPolyTime.binary_lt'

end LeanCanny
