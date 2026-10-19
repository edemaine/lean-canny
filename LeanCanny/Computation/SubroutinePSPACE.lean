/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SubroutineFunction

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

noncomputable def decider {L : Language} (P : Program) (hP : P.PolyTime)
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
    (hanswer : ∀ x, x ∈ L ↔ answer ((abstractStep P T)^[N x] (init x)) = true) :
    SpaceDecider L := by
  have E := evaluator P hP init hi H (fun p => [answer p]) hH ha T N r u w v
    hT hp hu hN hchild hbefore hafter
  have haccept : (fun bits : List Bool => [bits[0]?.getD false]) ∈ FP :=
    (FPPred.getBit id_mem_FP (UnaryFn.const 0)).flag_mem_FP
  refine E.decider (fun bits => bits[0]?.getD false) haccept ?_
  intro x
  simpa only [List.getElem?_cons_zero, Option.getD_some] using hanswer x

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
    (hanswer : ∀ x, x ∈ L ↔ answer ((abstractStep P T)^[N x] (init x)) = true) : L ∈ PSPACE :=
  (decider P hP init hi H answer hH ha T N r u w v hT hp hu hN hchild hbefore hafter hanswer).mem_PSPACE

end LeanCanny.Computation.SubroutineIteration
