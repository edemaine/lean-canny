/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.UnaryModularIteration
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Polynomially many modular sums and products at one counting level -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

@[expose] noncomputable def unaryModularSum (n p : ℕ) (v : ℕ → ℕ) : ℕ :=
  unaryModularIteration (fun _ : Unit => n) (fun _ => p)
    (fun q => q.2.2 + v q.2.1) ()

@[expose] noncomputable def unaryModularProduct (n p : ℕ) (v : ℕ → ℕ) : ℕ :=
  unaryModularIteration (fun _ : Unit => n + 1) (fun _ => p)
    (fun q => if q.2.1 = 0 then 1 else q.2.2 * v (q.2.1 - 1)) ()

theorem unaryModularSum_eq (n p : ℕ) (v : ℕ → ℕ) :
    unaryModularSum n p v = (∑ i ∈ Finset.range n, v i) % p := by
  have h (k : ℕ) :
      ((fun s : ℕ × ℕ => (s.1 + 1, (s.2 + v s.1) % p))^[k] (0, 0)) =
        (k, (∑ i ∈ Finset.range k, v i) % p) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Finset.sum_range_succ]
      simp [Nat.add_mod]
  exact congrArg Prod.snd (h n)

theorem unaryModularProduct_eq (n p : ℕ) (v : ℕ → ℕ) :
    unaryModularProduct n p v = (∏ i ∈ Finset.range n, v i) % p := by
  have h (k : ℕ) :
      ((fun s : ℕ × ℕ => (s.1 + 1,
        (if s.1 = 0 then 1 else s.2 * v (s.1 - 1)) % p))^[k + 1] (0, 0)) =
          (k + 1, (∏ i ∈ Finset.range k, v i) % p) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Finset.prod_range_succ]
      simp [Nat.mul_mod]
  exact congrArg Prod.snd (h n)

theorem unaryModularSum_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    {n p : α → ℕ} {v : α × ℕ → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hp : ComputableInPolyTime p enc encNat) (hpos : ∀ w, 0 < p w)
    (hv : v ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => unaryModularSum (n w) (p w) (fun i => v (w, i))) ∈
      CountingFunction a enc encNat := by
  have hvalue := CountingFunction.preprocess (input := encPair enc (encPair encNat encNat)) hv
    (g := fun q : α × (ℕ × ℕ) => (q.1, q.2.1)) (by fun_prop)
  have hacc : (fun q : α × (ℕ × ℕ) => q.2.2) ∈
      CountingFunction a (encPair enc (encPair encNat encNat)) encNat :=
    CountingFunction.of_polyTime (by fun_prop)
  have hadd := CountingFunction.map (CountingFunction.prod hacc hvalue)
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_add)
  have hout := unaryModularIteration_mem n p _ hn hp hpos hadd
  change (fun w => unaryModularIteration n p _ w) ∈ _ at hout
  exact hout

theorem unaryModularProduct_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    {n p : α → ℕ} {v : α × ℕ → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hp : ComputableInPolyTime p enc encNat) (hpos : ∀ w, 0 < p w)
    (hv : v ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => unaryModularProduct (n w) (p w) (fun i => v (w, i))) ∈
      CountingFunction a enc encNat := by
  have hi : ComputableInPolyTime (fun q : α × (ℕ × ℕ) => q.2.1)
      (encPair enc (encPair encNat encNat)) encNat := by fun_prop
  have hvalue := CountingFunction.preprocess hv
    ((ComputableInPolyTime.fst enc (encPair encNat encNat)).prod
      (ComputableInPolyTime.binary_sub' hi (.const 1)))
  have hacc : (fun q : α × (ℕ × ℕ) => q.2.2) ∈
      CountingFunction a (encPair enc (encPair encNat encNat)) encNat :=
    CountingFunction.of_polyTime (by fun_prop)
  have htest : ComputableInPolyTime
      (fun q : α × (ℕ × ℕ) => decide (q.2.1 = 0))
      (encPair enc (encPair encNat encNat)) encBool := by fun_prop
  have hstep := CountingFunction.ite (CountingFunction.of_polyTime htest)
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 1))
    (CountingFunction.nat_mul hacc hvalue)
  have hn' : ComputableInPolyTime (fun w => n w + 1) enc encUnary := by fun_prop
  simp only [decide_eq_true_eq] at hstep
  have hout := unaryModularIteration_mem (fun w => n w + 1) p _ hn' hp hpos hstep
  change (fun w => unaryModularIteration (fun w => n w + 1) p _ w) ∈ _ at hout
  exact hout

end LeanCanny.CountingHierarchy
