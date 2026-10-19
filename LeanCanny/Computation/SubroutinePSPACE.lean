/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SubroutineBounds

/-!
# Polynomial-space iteration with non-polynomial-time subroutine calls

Polynomial parent and child state lengths, together with exponential bounds
on parent steps and on each requested child run, give a PSPACE decision
procedure. Every physical step has an FP certificate. The resource hypotheses
are required only on the relevant parent run and its requested calls, not on
unreachable malformed states.
-/

@[expose] public section

namespace LeanCanny.Computation.SubroutineIteration
open Complexity

theorem mem_PSPACE {L : Language} (P : Program) (hP : P.PolyTime)
    (init : List Bool → List Bool) (hi : init ∈ FP)
    (H answer : List Bool → Bool)
    (hH : (fun p => [H p]) ∈ FP) (ha : (fun p => [answer p]) ∈ FP)
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
    (hafter : ∀ x, H ((abstractStep P T)^[N x] (init x)) = true)
    (hanswer : ∀ x, x ∈ L ↔ answer ((abstractStep P T)^[N x] (init x)) = true) : L ∈ PSPACE := by
  have hstart := mem_FP_comp hi (Cobham.cons_mem_FP false)
  have hans := mem_FP_comp (drop_mem_FP id_mem_FP (UnaryFn.const 1)) ha
  refine HaltingIteration.mem_PSPACE
    (init := fun x => parent (init x)) (advance := step P)
    (halt := halted H) (answer := fun bits => answer (bits.drop 1))
    hstart (step_mem_FP P hP) (halted_mem_FP hH) hans
    (2 * r + u + 3) (w + v + 2) (fun x => clock P T (init x) (N x)) ?_ ?_ ?_ ?_ ?_
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
    simpa only [parent, List.drop_succ_cons, List.drop_zero] using hanswer x

end LeanCanny.Computation.SubroutineIteration
