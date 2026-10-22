/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.RecursiveStackStepSpace

/-! # Uniform recursive evaluation in native polynomial space

One fixed local instruction routine and reply installer work at every rank.
Calls decrease rank; local continuations and installed replies decrease a
proof-only fuel measure. A binary FP fuel bound and unary FP rank bound give
an FP iteration budget. No execution times of the local computations appear.
-/

@[expose] public section

namespace LeanCanny.Computation.RecursiveStack
open Turing.MultiTapeTM

/-- Evaluate input-dependent recursion depth with one native space machine.
The validity predicate can retain the original input and need not be decidable.
Both `localStep` and `receive` may use arbitrary polynomial-space computations.
The fuel is a logical progress measure, not an execution clock for either one. -/
theorem evaluator {α F : Type} [Inhabited F] {encIn : α ↪ List Bool} {encF : F ↪ List Bool}
    {localStep : F → Action F} {receive : F × List Bool → F} {start : α → F}
    {value : F → List Bool} {rank fuel : F → ℕ} {valid : α → F → Prop} {N R B : α → ℕ}
    (hl : ComputableTidilyInPolySpace localStep encF (encAction encF))
    (hr : ComputableTidilyInPolySpace receive (encPair encF encBits) encF)
    (hs : ComputableTidilyInPolySpace start encIn encF)
    (hN : ComputableTidilyInPolyTime N encIn encNat)
    (hR : ComputableTidilyInPolyTime R encIn encUnary)
    (hB : PolyBounded (fun x => (encIn x).length) B)
    (rules : ∀ x, Rules localStep receive value rank fuel (valid x) (N x))
    (hstart : ∀ x, valid x (start x))
    (hrank : ∀ x p, valid x p → rank p ≤ R x)
    (hframe : ∀ x p, valid x p → (encF p).length ≤ B x)
    (hvalue : ∀ x p, valid x p → (value p).length ≤ B x) :
    ComputableTidilyInPolySpace (fun x => value (start x)) encIn encBits := by
  have hcount : ComputableTidilyInPolyTime (fun x => (N x + 2) ^ (R x + 1)) encIn encNat :=
    ComputableTidilyInPolyTime.binary_pow'
      (ComputableTidilyInPolyTime.binary_add' hN (ComputableTidilyInPolyTime.const 2))
      (ComputableTidilyInPolyTime.unary_add.comp (hR.prod (ComputableTidilyInPolyTime.const 1)))
  have hRbound : PolyBounded (fun x => (encIn x).length) R := by
    simpa only [encUnary_apply, List.length_replicate] using hR.polyBounded_length
  have hsize : PolyBounded (fun x => (encIn x).length)
      (fun x => 5 + 4 * B x + R x * (2 * B x + 1)) :=
    ((PolyBounded.const 5).add ((PolyBounded.const 4).mul hB)).add
      (hRbound.mul (((PolyBounded.const 2).mul hB).add (PolyBounded.const 1)))
  have hit := ComputableTidilyInPolySpace.iterate hcount (initial_computable hs)
    (step_computable encF hl hr) hsize (fun x k _ => by
      exact encoded_length_bound encF (hrank x) (hframe x) _
        (good_iterate (rules x) _ (good_initial _ _ _ _ _ (hstart x)) k)
        (output_length_iterate (rules x) (hvalue x) _ (hstart x) k))
  have hout : ComputableTidilyInPolyTime (fun s : State F => s.2.1) (encState encF) encBits := by
    fun_prop
  refine ((ComputableTidilyInPolySpace.of_polyTime hout).comp hit).congr fun x => ?_
  exact output_after (rules x) _ (good_initial _ _ _ _ _ (hstart x)) _
    (initial_potential_le (rules x) _ (hstart x) _ (hrank x _ (hstart x)))

end LeanCanny.Computation.RecursiveStack
