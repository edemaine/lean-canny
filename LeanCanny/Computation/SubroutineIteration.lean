/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.HaltingIteration

/-!
# Suspending an iteration while a subroutine runs

A parent state either takes an ordinary FP step or starts a child evaluator.
During a call, the parent is retained alongside the child's state. The child
uses an FP transition and halting test; resumption is also FP. An entire child
computation is never assumed to be polynomial time.

The abstract parent transition contracts a completed call into one step. Its
variable clock expands each call into initialization, child steps, and resume.
Correctness and resource estimates account for those steps explicitly.
-/

@[expose] public section

namespace LeanCanny.Computation.SubroutineIteration
open Complexity

structure Program where
  ordinary : List Bool → List Bool
  request : List Bool → Bool
  start : List Bool → List Bool
  advance : List Bool → List Bool
  halt : List Bool → Bool
  resume : List Bool → List Bool

structure Program.PolyTime (P : Program) : Prop where
  ordinary : P.ordinary ∈ FP
  request : (fun p => [P.request p]) ∈ FP
  start : P.start ∈ FP
  advance : P.advance ∈ FP
  halt : (fun u => [P.halt u]) ∈ FP
  resume : P.resume ∈ FP

def parent (p : List Bool) : List Bool := false :: p
def child (p u : List Bool) : List Bool := true :: pair p u

def step (P : Program) (bits : List Bool) : List Bool :=
  let body := bits.drop 1
  if bits[0]?.getD false = true then
    if P.halt (pairSnd body) then parent (P.resume body)
    else child (pairFst body) (P.advance (pairSnd body))
  else if P.request body then child body (P.start body)
  else parent (P.ordinary body)

theorem step_mem_FP (P : Program) (hP : P.PolyTime) : step P ∈ FP := by
  have hb := drop_mem_FP id_mem_FP (UnaryFn.const 1)
  have hp := mem_FP_comp hb pairFst_mem_FP
  have hu := mem_FP_comp hb pairSnd_mem_FP
  have hresume := mem_FP_comp (mem_FP_comp hb hP.resume) (Cobham.cons_mem_FP false)
  have hadvance := mem_FP_comp (mem_FP_pair hp (mem_FP_comp hu hP.advance))
    (Cobham.cons_mem_FP true)
  have hchild := ((FPPred.of_flag hP.halt).comp hu).ite_mem_FP hresume hadvance
  have hstart := mem_FP_comp (mem_FP_pair hb (mem_FP_comp hb hP.start))
    (Cobham.cons_mem_FP true)
  have hord := mem_FP_comp (mem_FP_comp hb hP.ordinary) (Cobham.cons_mem_FP false)
  have hparent := ((FPPred.of_flag hP.request).comp hb).ite_mem_FP hstart hord
  have h := (FPPred.getBit id_mem_FP (UnaryFn.const 0)).ite_mem_FP hchild hparent
  exact mem_FP_of_eq h (fun _ => rfl)

theorem step_parent (P : Program) (p : List Bool) : step P (parent p) =
    if P.request p then child p (P.start p) else parent (P.ordinary p) := by
  simp [step, parent]

theorem step_child (P : Program) (p u : List Bool) : step P (child p u) =
    if P.halt u then parent (P.resume (pair p u)) else child p (P.advance u) := by
  simp [step, child]

structure TerminatesAt (P : Program) (p : List Bool) (T : ℕ) : Prop where
  before : ∀ t, t < T → P.halt (P.advance^[t] (P.start p)) = false
  after : P.halt (P.advance^[T] (P.start p)) = true

def abstractStep (P : Program) (T : List Bool → ℕ) (p : List Bool) : List Bool :=
  if P.request p then P.resume (pair p (P.advance^[T p] (P.start p))) else P.ordinary p

def cost (P : Program) (T : List Bool → ℕ) (p : List Bool) : ℕ :=
  if P.request p then T p + 2 else 1

theorem cost_pos (P : Program) (T : List Bool → ℕ) (p : List Bool) : 0 < cost P T p := by
  simp only [cost]
  split_ifs <;> omega

theorem iterate_child (P : Program) (p : List Bool) (T : ℕ)
    (hT : TerminatesAt P p T) (t : ℕ) (ht : t ≤ T) :
    (step P)^[t] (child p (P.start p)) = child p (P.advance^[t] (P.start p)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih (by omega), step_child, hT.before t (by omega)]
      simp only [Bool.false_eq_true, ↓reduceIte, Function.iterate_succ_apply']

theorem iterate_call (P : Program) (p : List Bool) (T : ℕ) (hT : TerminatesAt P p T) :
    (step P)^[T + 1] (child p (P.start p)) =
      parent (P.resume (pair p (P.advance^[T] (P.start p)))) := by
  rw [Function.iterate_succ_apply', iterate_child P p T hT T le_rfl, step_child, hT.after]
  rfl

theorem iterate_operation (P : Program) (T : List Bool → ℕ) (p : List Bool)
    (hT : P.request p = true → TerminatesAt P p (T p)) :
    (step P)^[cost P T p] (parent p) = parent (abstractStep P T p) := by
  by_cases hr : P.request p = true
  · simp only [cost, abstractStep, hr, ↓reduceIte]
    rw [show T p + 2 = (T p + 1) + 1 by omega, Function.iterate_add_apply,
      Function.iterate_one, step_parent, hr]
    simpa using iterate_call P p (T p) (hT hr)
  · simp [cost, abstractStep, hr, step_parent]

def clock (P : Program) (T : List Bool → ℕ) (p : List Bool) : ℕ → ℕ
  | 0 => 0
  | N + 1 => cost P T ((abstractStep P T)^[N] p) + clock P T p N

theorem iterate_clock (P : Program) (T : List Bool → ℕ) (p : List Bool) (N : ℕ)
    (hT : ∀ k, k < N → P.request ((abstractStep P T)^[k] p) = true →
      TerminatesAt P ((abstractStep P T)^[k] p) (T ((abstractStep P T)^[k] p))) :
    (step P)^[clock P T p N] (parent p) = parent ((abstractStep P T)^[N] p) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [clock, Function.iterate_add_apply, ih (by intro k hk; exact hT k (by omega)),
        iterate_operation P T _ (hT N (by omega)), Function.iterate_succ_apply']

theorem clock_le (P : Program) (T : List Bool → ℕ) (p : List Bool) (N U : ℕ)
    (hT : ∀ k, k < N → P.request ((abstractStep P T)^[k] p) = true →
      T ((abstractStep P T)^[k] p) ≤ U) : clock P T p N ≤ N * (U + 2) := by
  induction N with
  | zero => simp [clock]
  | succ N ih =>
      have hi := ih (by intro k hk; exact hT k (by omega))
      have hc : cost P T ((abstractStep P T)^[N] p) ≤ U + 2 := by
        unfold cost
        split_ifs with hr
        · exact Nat.add_le_add_right (hT N (by omega) hr) 2
        · omega
      rw [clock, Nat.succ_mul]
      omega

end LeanCanny.Computation.SubroutineIteration
