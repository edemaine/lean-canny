/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Complexitylib.Interop.Cslib.MultiTape
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import LeanCanny.Encoding.BinaryNatFP

/-! # Reusing existing FP certificates in the tidy calculus

The machine bridge preserves the existing raw binary codecs. Pair construction
also has a typed interface, so new space proofs can retain typed states.
-/

@[expose] public section

namespace LeanCanny.Computation.TidyFP

open Turing.MultiTapeTM

theorem of_mem_FP {f : List Bool → List Bool} (hf : f ∈ Complexity.FP) :
    ComputableTidilyInPolyTime f encBits encBits := by
  obtain ⟨p, h⟩ := Complexity.computableInTimeAndSpace_of_mem_FP hf
  obtain ⟨c, h⟩ := h.exists_computableTidilyInTimeAndSpace
  have hp : PolyBounded (fun x : List Bool => x.length) (fun x => p.eval x.length) :=
    PolyBounded.of_polynomiallyBounded _ (.polynomial_eval p)
  exact ⟨_, _, (((PolyBounded.const 2).mul hp).add ((PolyBounded.const 3).mul hp)).add
    (PolyBounded.const c), (PolyBounded.const c).mul (hp.add (PolyBounded.const 1)), h⟩

theorem of_flag {f : List Bool → Bool} (hf : (fun x => [f x]) ∈ Complexity.FP) :
    ComputableTidilyInPolyTime f encBits encBool :=
  (of_mem_FP hf).of_enc_eq fun _ => rfl

private def delimitT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [b, b])
  final _ := [false, true]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem delimitT_run (w : List Bool) : delimitT.run () w = Complexity.delimit w := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [Transducer.run_cons, ih, Complexity.delimit_cons]; rfl

theorem delimit : ComputableTidilyInPolyTime Complexity.delimit encBits encBits := by
  refine ComputableTidilyInPolyTime.of_linear ⟨8, ?_⟩
  exact (delimitT.computableTidilyInTimeAndSpace fun w => (delimitT_run w).symm).mono
    (fun w => by simp only [encBits_apply]; omega) (fun _ => Nat.zero_le _)

theorem pair {α : Type} {enc : α ↪ List Bool} {f g : α → List Bool}
    (hf : ComputableTidilyInPolyTime f enc encBits)
    (hg : ComputableTidilyInPolyTime g enc encBits) :
    ComputableTidilyInPolyTime (fun a => Complexity.pair (f a) (g a)) enc encBits :=
  (delimit.comp hf).append hg fun _ => rfl

theorem fromBitsLE : ComputableTidilyInPolyTime Nat.fromBitsLE encBits encNat :=
  (of_mem_FP Encoding.BinaryNat.normalize_mem_FP).of_enc_eq fun w =>
    (Encoding.BinaryNat.normalize_eq_bits w).symm

theorem natBits : ComputableTidilyInPolyTime Nat.bits encNat encBits :=
  .of_eq fun _ => rfl

end LeanCanny.Computation.TidyFP
