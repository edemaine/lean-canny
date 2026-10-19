/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SubroutineBounds
public import LeanCanny.Computation.SpaceFunction

/-!
# Certified output from suspended iteration

Polynomial parent/child state bounds and exponential parent/child clocks give
a reusable output evaluator. The output projection is FP; the complete child
computation need not be. Every intermediate physical state is covered by the
existing suspended-prefix classification.
-/

@[expose] public section

namespace LeanCanny.Computation.SubroutineIteration
open Complexity

noncomputable def evaluator (P : Program) (hP : P.PolyTime)
    (init : List Bool → List Bool) (hi : init ∈ FP)
    (H : List Bool → Bool) (output : List Bool → List Bool)
    (hH : (fun p => [H p]) ∈ FP) (ho : output ∈ FP)
    (T : List Bool → ℕ) (N : List Bool → ℕ) (r u w v : Polynomial ℕ)
    (hT : ∀ x k, k < N x → P.request ((abstractStep P T)^[k] (init x)) = true →
      TerminatesAt P ((abstractStep P T)^[k] (init x)) (T ((abstractStep P T)^[k] (init x))))
    (hp : ∀ x k, k ≤ N x → ((abstractStep P T)^[k] (init x)).length ≤ r.eval x.length)
    (hu : ∀ x k, k < N x → P.request ((abstractStep P T)^[k] (init x)) = true →
      ∀ j, j ≤ T ((abstractStep P T)^[k] (init x)) →
        (P.advance^[j] (P.start ((abstractStep P T)^[k] (init x)))).length ≤ u.eval x.length)
    (hN : ∀ x, N x ≤ 2 ^ w.eval x.length)
    (hchild : ∀ x k, k < N x → P.request ((abstractStep P T)^[k] (init x)) = true →
      T ((abstractStep P T)^[k] (init x)) ≤ 2 ^ v.eval x.length)
    (hbefore : ∀ x k, k < N x → H ((abstractStep P T)^[k] (init x)) = false)
    (hafter : ∀ x, H ((abstractStep P T)^[N x] (init x)) = true) :
    SpaceFunction (fun x => output ((abstractStep P T)^[N x] (init x))) := by
  have hstart := mem_FP_comp hi (Cobham.cons_mem_FP false)
  have hout := mem_FP_comp (drop_mem_FP id_mem_FP (UnaryFn.const 1)) ho
  refine { init := fun x => parent (init x)
           advance := step P
           halt := halted H
           output := fun bits => output (bits.drop 1)
           initFP := hstart
           advanceFP := step_mem_FP P hP
           haltFP := halted_mem_FP hH
           outputFP := hout
           space := 2 * r + u + 3
           clock := w + v + 2
           time := fun x => clock P T (init x) (N x)
           length_le := ?_
           time_le := ?_
           before := ?_
           after := ?_
           correct := ?_ }
  · intro x t ht
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat] using
      iterate_length_le P T (init x) (N x) (r.eval x.length) (u.eval x.length)
        (hT x) (hp x) (hu x) t ht
  · intro x
    have hc := clock_le P T (init x) (N x) (2 ^ v.eval x.length) (hchild x)
    have hv : 2 ^ v.eval x.length + 2 ≤ 2 ^ v.eval x.length * 4 := by
      have hpos : 0 < 2 ^ v.eval x.length := pow_pos (by decide) _
      omega
    have h := hc.trans (Nat.mul_le_mul (hN x) hv)
    simpa only [Polynomial.eval_add, Polynomial.eval_ofNat, pow_add,
      show (2 : ℕ) ^ 2 = 4 from rfl, Nat.mul_assoc] using h
  · intro x t ht
    exact halted_before P T (init x) (N x) (hT x) H (hbefore x) t ht
  · intro x
    rw [iterate_clock P T (init x) (N x) (hT x), halted_parent]
    exact hafter x
  · intro x
    rw [iterate_clock P T (init x) (N x) (hT x)]
    simp only [parent, List.drop_succ_cons, List.drop_zero]

end LeanCanny.Computation.SubroutineIteration
