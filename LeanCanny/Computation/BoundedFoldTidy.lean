/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFold
public import LeanCanny.Computation.TidyBoundedFold
public import LeanCanny.Computation.TidyFP

/-! # The existing raw-code fold in the tidy space calculus

This certifies the same fold and packet encoding as the legacy evaluator. The
child is only assumed polynomial-space computable; no child clocks or explicit
controller certificate are needed. The typed iteration retains the context.
-/

@[expose] public section

namespace LeanCanny.Computation.BoundedFold

open Turing.MultiTapeTM

theorem packet_polyTime :
    ComputableTidilyInPolyTime (fun p : List Bool × ℕ × List Bool => packet p.1 p.2.1 p.2.2)
      (TidyBoundedFold.encPacket encBits encBits) encBits := by
  have hc := ComputableTidilyInPolyTime.fst encBits (encPair encNat encBits)
  have hr := ComputableTidilyInPolyTime.snd encBits (encPair encNat encBits)
  exact TidyFP.pair hc (TidyFP.pair (TidyFP.natBits.comp hr.fst') hr.snd')

theorem typed_fold_eq (f seed : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    TidyBoundedFold.fold (fun p => f (packet p.1 p.2.1 p.2.2)) seed c k = fold f seed c k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [TidyBoundedFold.fold, fold, ih]

/-- A replacement space certificate for `evaluator`, using the identical raw-code fold. -/
theorem computable {f : List Bool → List Bool}
    (hf : ComputableTidilyInPolySpace f encBits encBits)
    (bound seed : List Bool → List Bool) (hb : bound ∈ Complexity.FP) (hs : seed ∈ Complexity.FP)
    (s : Polynomial ℕ)
    (hstate : ∀ c i, i ≤ Nat.fromBitsLE (bound c) → (fold f seed c i).length ≤ s.eval c.length) :
    ComputableTidilyInPolySpace (fun c => fold f seed c (Nat.fromBitsLE (bound c)))
      encBits encBits := by
  have hchild := hf.comp (ComputableTidilyInPolySpace.of_polyTime packet_polyTime)
  have hcount := TidyFP.fromBitsLE.comp (TidyFP.of_mem_FP hb)
  have hseed := ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_mem_FP hs)
  have h := TidyBoundedFold.evaluator hchild hcount hseed
    (B := fun c => s.eval c.length)
    (PolyBounded.of_polynomiallyBounded _ (.polynomial_eval s)) (fun c i hi => by
      rw [typed_fold_eq]
      exact hstate c i hi)
  exact h.congr fun c => typed_fold_eq f seed c _

end LeanCanny.Computation.BoundedFold
