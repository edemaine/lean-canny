/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFold
public import LeanCanny.Computation.TidyBoundedFold
public import LeanCanny.Computation.SpaceFunctionComposition

/-! # Bounded folds in the tidy space calculus

The child receives the existing raw context/index/accumulator packet. Native
composition and typed binary iteration certify the fold directly.
Only the mathematical accumulator-prefix bound is required. -/

@[expose] public section

namespace LeanCanny.Computation.BoundedFold

open Turing.MultiTapeTM

theorem packet_polyTime :
    ComputableTidilyInPolyTime (fun p : List Bool × ℕ × List Bool => packet p.1 p.2.1 p.2.2)
      (TidyBoundedFold.encPacket encBits encBits) encBits := by
  have hc := ComputableTidilyInPolyTime.fst encBits (encPair encNat encBits)
  have hr := ComputableTidilyInPolyTime.snd encBits (encPair encNat encBits)
  exact pair_computable hc (pair_computable (natBits_computable.comp hr.fst') hr.snd')

theorem typed_fold_eq (f seed : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    TidyBoundedFold.fold (fun p => f (packet p.1 p.2.1 p.2.2)) seed c k = fold f seed c k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [TidyBoundedFold.fold, fold, ih]

/-- Polynomial-space evaluation of the existing raw-code fold. -/
theorem evaluator {f : List Bool → List Bool}
    (E : SpaceFunction f)
    (bound seed : List Bool → List Bool) (hb : bound ∈ LeanCanny.FP) (hs : seed ∈ LeanCanny.FP)
    (s : Polynomial ℕ)
    (hstate : ∀ c i, i ≤ Nat.fromBitsLE (bound c) → (fold f seed c i).length ≤ s.eval c.length) :
    SpaceFunction (fun c => fold f seed c (Nat.fromBitsLE (bound c))) := by
  have hchild := E.computable.comp (ComputableTidilyInPolySpace.of_polyTime packet_polyTime)
  have hcount := fromBitsLE_computable.comp (FP.computable hb)
  have hseed := ComputableTidilyInPolySpace.of_polyTime (FP.computable hs)
  have h := TidyBoundedFold.evaluator hchild hcount hseed
    (B := fun c => s.eval c.length)
    (PolyBounded.of_polynomiallyBounded _ (.polynomial_eval s)) (fun c i hi => by
      rw [typed_fold_eq]
      exact hstate c i hi)
  exact ⟨h.congr fun c => typed_fold_eq f seed c _⟩

end LeanCanny.Computation.BoundedFold
