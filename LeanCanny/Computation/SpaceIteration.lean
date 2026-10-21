/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionBranch
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Iterating space-bounded transitions

Binary-counted iteration is the native library rule. For semantic controllers
whose stopping index is not computed, freezing at the first terminal state
allows any certified binary upper bound. Child execution times never enter.
-/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction
open Complexity Turing.MultiTapeTM

theorem iterate {step : List Bool → List Bool} (E : SpaceFunction step)
    (init count : List Bool → List Bool) (hi : init ∈ FP) (hc : count ∈ FP)
    (s : Polynomial ℕ)
    (hstate : ∀ x k, k ≤ Nat.fromBitsLE (count x) →
      (step^[k] (init x)).length ≤ s.eval x.length) :
    SpaceFunction (fun x => step^[Nat.fromBitsLE (count x)] (init x)) :=
  ⟨ComputableTidilyInPolySpace.iterate
    (TidyFP.fromBitsLE.comp (TidyFP.of_mem_FP hc))
    (ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_mem_FP hi)) E.computable
    (PolyBounded.of_polynomiallyBounded _ (.polynomial_eval s)) hstate⟩

private def freeze (step : List Bool → List Bool) (halt : List Bool → Bool) (x : List Bool) :=
  if halt x then x else step x

private theorem freeze_iterate (step : List Bool → List Bool) (halt : List Bool → Bool)
    (x : List Bool) (N : ℕ)
    (hb : ∀ k < N, halt (step^[k] x) = false) (ha : halt (step^[N] x) = true) (k : ℕ) :
    (freeze step halt)^[k] x = step^[min k N] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hk : k < N
    · rw [Nat.min_eq_left hk.le, Nat.min_eq_left (Nat.succ_le_of_lt hk)]
      simp only [freeze, hb k hk, Bool.false_eq_true, ↓reduceIte, Function.iterate_succ_apply']
    · have hN : N ≤ k := Nat.le_of_not_gt hk
      rw [Nat.min_eq_right hN, Nat.min_eq_right (hN.trans (Nat.le_succ k))]
      simp only [freeze, ha, ↓reduceIte]

theorem orbit {step : List Bool → List Bool} (E : SpaceFunction step)
    (init : List Bool → List Bool) (hi : init ∈ FP)
    (halt : List Bool → Bool) (output : List Bool → List Bool)
    (hh : (fun x => [halt x]) ∈ FP) (ho : output ∈ FP)
    (N : List Bool → ℕ) (s w : Polynomial ℕ)
    (hstate : ∀ x k, k ≤ N x → (step^[k] (init x)).length ≤ s.eval x.length)
    (hN : ∀ x, N x ≤ 2 ^ w.eval x.length)
    (hb : ∀ x k, k < N x → halt (step^[k] (init x)) = false)
    (ha : ∀ x, halt (step^[N x] (init x)) = true) :
    SpaceFunction (fun x => output (step^[N x] (init x))) := by
  have hlength : ComputableTidilyInPolyTime List.length encBits encUnary :=
    ComputableTidilyInPolyTime.length encBool
  have hcount := ComputableTidilyInPolyTime.binary_two_pow.comp
    ((ComputableTidilyInPolyTime.unary_eval w).comp hlength)
  have hstep : ComputableTidilyInPolySpace (freeze step halt) encBits encBits :=
    (ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_flag hh)).ite
      ComputableTidilyInPolySpace.id' E.computable
  have h := ComputableTidilyInPolySpace.iterate hcount
    (ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_mem_FP hi)) hstep
    (B := fun x => s.eval x.length)
    (PolyBounded.of_polynomiallyBounded _ (.polynomial_eval s)) (fun x k _ => by
      rw [freeze_iterate step halt _ _ (hb x) (ha x)]
      exact hstate x _ (Nat.min_le_right _ _))
  refine ⟨((ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_mem_FP ho)).comp h).congr
    fun x => ?_⟩
  simp only [Function.comp_apply]
  rw [freeze_iterate step halt _ _ (hb x) (ha x), Nat.min_eq_right (hN x)]

end LeanCanny.Computation.SpaceFunction
