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

/-- The standard context/index query, with the raw decoder's total behavior. -/
def query (p : List Bool) : List Bool := pair (pairFst p) (counter p)

def update (finish f : List Bool → List Bool) (p : List Bool) : List Bool :=
  finish (pair p (f (query p)))

theorem query_mem_FP : query ∈ FP := mem_FP_pair pairFst_mem_FP counter_mem_FP

theorem updateEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (finish : List Bool → List Bool) (hf : finish ∈ FP) : SpaceFunction (update finish f) :=
  E.call query finish query_mem_FP hf

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

/-- Raw-code fold evaluation with a native bound in the original input. -/
theorem evaluator_polyBounded {f : List Bool → List Bool} {B : List Bool → ℕ}
    (E : SpaceFunction f)
    (bound seed : List Bool → List Bool) (hb : bound ∈ LeanCanny.FP) (hs : seed ∈ LeanCanny.FP)
    (hB : PolyBounded List.length B)
    (hstate : ∀ c i, i ≤ Nat.fromBitsLE (bound c) → (fold f seed c i).length ≤ B c) :
    SpaceFunction (fun c => fold f seed c (Nat.fromBitsLE (bound c))) := by
  have hchild := E.computable.comp (ComputableTidilyInPolySpace.of_polyTime packet_polyTime)
  have hcount := fromBitsLE_computable.comp (FP.computable hb)
  have hseed := ComputableTidilyInPolySpace.of_polyTime (FP.computable hs)
  have h := TidyBoundedFold.evaluator hchild hcount hseed
    (B := B) (by simpa only [encBits_apply] using hB) (fun c i hi => by
      rw [typed_fold_eq]
      exact hstate c i hi)
  exact ⟨h.congr fun c => typed_fold_eq f seed c _⟩

/-- Compatibility adapter for callers supplying an explicit polynomial. -/
theorem evaluator {f : List Bool → List Bool}
    (E : SpaceFunction f)
    (bound seed : List Bool → List Bool) (hb : bound ∈ LeanCanny.FP) (hs : seed ∈ LeanCanny.FP)
    (s : Polynomial ℕ)
    (hstate : ∀ c i, i ≤ Nat.fromBitsLE (bound c) → (fold f seed c i).length ≤ s.eval c.length) :
    SpaceFunction (fun c => fold f seed c (Nat.fromBitsLE (bound c))) :=
  evaluator_polyBounded E bound seed hb hs
    (PolyBounded.of_polynomiallyBounded _ (.polynomial_eval s)) hstate

theorem fold_spec {f seed bound : List Bool → List Bool}
    (v : List Bool → ℕ → List Bool) (hseed : ∀ c, seed c = v c 0)
    (hstep : ∀ c k, k < Nat.fromBitsLE (bound c) → f (packet c k (v c k)) = v c (k + 1))
    (c : List Bool) (k : ℕ) (hk : k ≤ Nat.fromBitsLE (bound c)) :
    fold f seed c k = v c k := by
  rw [← typed_fold_eq]
  exact TidyBoundedFold.fold_spec v hseed hstep c k hk

/-- Lift a semantic prefix sequence directly to its final space certificate. -/
theorem evaluator_spec {f : List Bool → List Bool} {B : List Bool → ℕ}
    (E : SpaceFunction f) (bound seed : List Bool → List Bool) (hb : bound ∈ FP) (hs : seed ∈ FP)
    (v : List Bool → ℕ → List Bool) (hseed : ∀ c, seed c = v c 0)
    (hstep : ∀ c k, k < Nat.fromBitsLE (bound c) → f (packet c k (v c k)) = v c (k + 1))
    (hB : PolyBounded List.length B)
    (hstate : ∀ c k, k ≤ Nat.fromBitsLE (bound c) → (v c k).length ≤ B c) :
    SpaceFunction (fun c => v c (Nat.fromBitsLE (bound c))) := by
  have h := evaluator_polyBounded E bound seed hb hs hB (fun c k hk => by
    rw [fold_spec v hseed hstep c k hk]
    exact hstate c k hk)
  exact h.congr (funext fun c => fold_spec v hseed hstep c _ le_rfl)

/-- Semantic lift for an existing prefix equation. -/
theorem evaluator_eq {f : List Bool → List Bool} {B : List Bool → ℕ}
    (E : SpaceFunction f) (bound seed : List Bool → List Bool) (hb : bound ∈ FP) (hs : seed ∈ FP)
    (v : List Bool → ℕ → List Bool)
    (hfold : ∀ c k, k ≤ Nat.fromBitsLE (bound c) → fold f seed c k = v c k)
    (hB : PolyBounded List.length B)
    (hstate : ∀ c k, k ≤ Nat.fromBitsLE (bound c) → (v c k).length ≤ B c) :
    SpaceFunction (fun c => v c (Nat.fromBitsLE (bound c))) := by
  apply evaluator_spec E bound seed hb hs v
    (fun c => hfold c 0 (Nat.zero_le _)) _ hB hstate
  intro c k hk
  calc
    f (packet c k (v c k)) = f (packet c k (fold f seed c k)) :=
      congrArg (fun a => f (packet c k a)) (hfold c k (by omega)).symm
    _ = fold f seed c (k + 1) := rfl
    _ = v c (k + 1) := hfold c (k + 1) (by omega)

end LeanCanny.Computation.BoundedFold
