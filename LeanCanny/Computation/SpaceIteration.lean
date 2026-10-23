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

namespace Turing.MultiTapeTM.ComputableTidilyInPolySpace

private def freeze {β : Type} (step : β → β) (halt : β → Bool) (x : β) :=
  if halt x then x else step x

private theorem freeze_iterate {β : Type} (step : β → β) (halt : β → Bool)
    (x : β) (N : ℕ)
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

/-- A proof-only stopping index and polynomial envelopes suffice for a native
space orbit. Initialization, transitions, tests, and output may all use space. -/
theorem orbit_of_polyBounded {α β γ : Type} [Inhabited β]
    {encIn : α ↪ List Bool} {encState : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {step : β → β} {init : α → β} {halt : β → Bool} {output : β → γ}
    (hi : ComputableTidilyInPolySpace init encIn encState)
    (hs : ComputableTidilyInPolySpace step encState encState)
    (hh : ComputableTidilyInPolySpace halt encState encBool)
    (ho : ComputableTidilyInPolySpace output encState encOut)
    (N B W : α → ℕ)
    (hB : PolyBounded (fun x => (encIn x).length) B)
    (hW : PolyBounded (fun x => (encIn x).length) W)
    (hstate : ∀ x k, k ≤ N x → (encState (step^[k] (init x))).length ≤ B x)
    (hN : ∀ x, N x ≤ 2 ^ W x)
    (hb : ∀ x k, k < N x → halt (step^[k] (init x)) = false)
    (ha : ∀ x, halt (step^[N x] (init x)) = true) :
    ComputableTidilyInPolySpace (fun x => output (step^[N x] (init x))) encIn encOut := by
  obtain ⟨w, hw⟩ := hW.exists_polynomial
  have hlength : ComputableTidilyInPolyTime (fun x => (encIn x).length) encIn encUnary :=
    ComputableTidilyInPolyTime.length_bits.comp (ComputableTidilyInPolyTime.encode encIn)
  have hcount := ComputableTidilyInPolyTime.binary_two_pow.comp
    ((ComputableTidilyInPolyTime.unary_eval w).comp hlength)
  have hstep : ComputableTidilyInPolySpace (freeze step halt) encState encState :=
    hh.ite id' hs
  have h := iterate hcount hi hstep hB (fun x k _ => by
    rw [freeze_iterate step halt _ _ (hb x) (ha x)]
    exact hstate x _ (Nat.min_le_right _ _))
  refine (ho.comp h).congr fun x => ?_
  simp only [Function.comp_apply]
  rw [freeze_iterate step halt _ _ (hb x) (ha x),
    Nat.min_eq_right ((hN x).trans (Nat.pow_le_pow_right (by decide) (hw x))) ]

end Turing.MultiTapeTM.ComputableTidilyInPolySpace

namespace LeanCanny.Computation.SpaceFunction
open Turing.MultiTapeTM

/-- Binary-counted iteration with a native growth certificate for the live state.
The bound itself need not be computed by the machine. -/
theorem iterate_of_polyBounded {step : List Bool → List Bool} (E : SpaceFunction step)
    (init count : List Bool → List Bool) (hi : init ∈ FP) (hc : count ∈ FP)
    (bound : List Bool → ℕ) (hbound : PolyBounded List.length bound)
    (hstate : ∀ x k, k ≤ Nat.fromBitsLE (count x) →
      (step^[k] (init x)).length ≤ bound x) :
    SpaceFunction (fun x => step^[Nat.fromBitsLE (count x)] (init x)) :=
  ⟨ComputableTidilyInPolySpace.iterate
    (fromBitsLE_computable.comp (FP.computable hc))
    (ComputableTidilyInPolySpace.of_polyTime (FP.computable hi)) E.computable
    hbound hstate⟩

theorem iterate {step : List Bool → List Bool} (E : SpaceFunction step)
    (init count : List Bool → List Bool) (hi : init ∈ FP) (hc : count ∈ FP)
    (s : Polynomial ℕ)
    (hstate : ∀ x k, k ≤ Nat.fromBitsLE (count x) →
      (step^[k] (init x)).length ≤ s.eval x.length) :
    SpaceFunction (fun x => step^[Nat.fromBitsLE (count x)] (init x)) :=
  E.iterate_of_polyBounded init count hi hc (fun x => s.eval x.length)
    (PolyBounded.of_polynomiallyBounded _ (.polynomial_eval s)) hstate

/-- Raw-word compatibility for the encoding-parametric orbit certificate. -/
theorem orbit_of_polyBounded {step : List Bool → List Bool} (E : SpaceFunction step)
    (init : List Bool → List Bool) (hi : init ∈ FP)
    (halt : List Bool → Bool) (output : List Bool → List Bool)
    (hh : (fun x => [halt x]) ∈ FP) (ho : output ∈ FP)
    (N B W : List Bool → ℕ) (hB : PolyBounded List.length B) (hW : PolyBounded List.length W)
    (hstate : ∀ x k, k ≤ N x → (step^[k] (init x)).length ≤ B x)
    (hN : ∀ x, N x ≤ 2 ^ W x)
    (hb : ∀ x k, k < N x → halt (step^[k] (init x)) = false)
    (ha : ∀ x, halt (step^[N x] (init x)) = true) :
    SpaceFunction (fun x => output (step^[N x] (init x))) :=
  ⟨ComputableTidilyInPolySpace.orbit_of_polyBounded (.of_polyTime hi) E.computable
    (.of_polyTime (flag_computable hh)) (.of_polyTime ho) N B W hB hW hstate hN hb ha⟩

theorem orbit {step : List Bool → List Bool} (E : SpaceFunction step)
    (init : List Bool → List Bool) (hi : init ∈ FP)
    (halt : List Bool → Bool) (output : List Bool → List Bool)
    (hh : (fun x => [halt x]) ∈ FP) (ho : output ∈ FP)
    (N : List Bool → ℕ) (s w : Polynomial ℕ)
    (hstate : ∀ x k, k ≤ N x → (step^[k] (init x)).length ≤ s.eval x.length)
    (hN : ∀ x, N x ≤ 2 ^ w.eval x.length)
    (hb : ∀ x k, k < N x → halt (step^[k] (init x)) = false)
    (ha : ∀ x, halt (step^[N x] (init x)) = true) :
    SpaceFunction (fun x => output (step^[N x] (init x))) :=
  E.orbit_of_polyBounded init hi halt output hh ho N
    (fun x => s.eval x.length) (fun x => w.eval x.length)
    (PolyBounded.of_polynomiallyBounded _ (.polynomial_eval s))
    (PolyBounded.of_polynomiallyBounded _ (.polynomial_eval w)) hstate hN hb ha

end LeanCanny.Computation.SpaceFunction
