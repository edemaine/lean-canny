/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Complexitylib.Classes.P
public import Complexitylib.Classes.P.StringAccess
public import Complexitylib.Classes.P.Pairing
public import Complexitylib.Classes.Space.Iterate

/-!
# Polynomial-space iteration with a halting test

An FP initializer and transition can be iterated for an input-dependent number
of steps, with an FP halting test and one-bit answer. Polynomial state bounds
and an exponential time bound yield membership in Complexitylib's PSPACE.
The wrapper proves the exact completion/answer protocol required by SpaceIter.
The time bound is a proof parameter; the transition does not compute its clock.
-/

@[expose] public section

namespace LeanCanny.Computation.HaltingIteration
open Complexity

def running (s : List Bool) : List Bool := false :: false :: s
def finished (s : List Bool) : List Bool := true :: s

def step (init advance : List Bool → List Bool) (halt answer : List Bool → Bool)
    (bits : List Bool) : List Bool :=
  if bits[0]?.getD false = true then [answer (bits.drop 1)]
  else if bits[1]?.getD false = true then running (init (bits.drop 2))
  else if halt (bits.drop 2) then finished (bits.drop 2)
  else running (advance (bits.drop 2))

theorem step_mem_FP {init advance : List Bool → List Bool} {halt answer : List Bool → Bool}
    (hi : init ∈ FP) (ha : advance ∈ FP)
    (hh : (fun s => [halt s]) ∈ FP) (hr : (fun s => [answer s]) ∈ FP) :
    step init advance halt answer ∈ FP := by
  have hd1 := drop_mem_FP id_mem_FP (UnaryFn.const 1)
  have hd2 := drop_mem_FP id_mem_FP (UnaryFn.const 2)
  have hexit := mem_FP_comp hd1 hr
  have hinit := mem_FP_comp (mem_FP_comp (mem_FP_comp hd2 hi) (Cobham.cons_mem_FP false))
    (Cobham.cons_mem_FP false)
  have hdone := mem_FP_comp hd2 (Cobham.cons_mem_FP true)
  have hnext := mem_FP_comp (mem_FP_comp (mem_FP_comp hd2 ha) (Cobham.cons_mem_FP false))
    (Cobham.cons_mem_FP false)
  have hloop := ((FPPred.of_flag hh).comp hd2).ite_mem_FP hdone hnext
  have hstart := (FPPred.getBit id_mem_FP (UnaryFn.const 1)).ite_mem_FP hinit hloop
  have h := (FPPred.getBit id_mem_FP (UnaryFn.const 0)).ite_mem_FP hexit hstart
  exact mem_FP_of_eq h (fun _ => rfl)

theorem step_initial (init advance : List Bool → List Bool) (halt answer : List Bool → Bool)
    (x : List Bool) : step init advance halt answer (pair [] x) = running (init x) := by
  simp [step, pair]

theorem step_running (init advance : List Bool → List Bool) (halt answer : List Bool → Bool)
    (s : List Bool) : step init advance halt answer (running s) =
      if halt s then finished s else running (advance s) := by simp [step, running]

theorem step_finished (init advance : List Bool → List Bool) (halt answer : List Bool → Bool)
    (s : List Bool) : step init advance halt answer (finished s) = [answer s] := by
  simp [step, finished]

theorem iterate_running (init advance : List Bool → List Bool) (halt answer : List Bool → Bool)
    (T : List Bool → ℕ)
    (hbefore : ∀ x t, t < T x → halt (advance^[t] (init x)) = false)
    (x : List Bool) (t : ℕ) (ht : t ≤ T x) :
    (step init advance halt answer)^[t + 1] (pair [] x) = running (advance^[t] (init x)) := by
  induction t with
  | zero => simpa using step_initial init advance halt answer x
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih (by omega), step_running, hbefore x t (by omega)]
      simp only [Bool.false_eq_true, ↓reduceIte, Function.iterate_succ_apply']

theorem iterate_finished (init advance : List Bool → List Bool) (halt answer : List Bool → Bool)
    (T : List Bool → ℕ)
    (hbefore : ∀ x t, t < T x → halt (advance^[t] (init x)) = false)
    (hafter : ∀ x, halt (advance^[T x] (init x)) = true) (x : List Bool) :
    (step init advance halt answer)^[T x + 2] (pair [] x) = finished (advance^[T x] (init x)) := by
  rw [show T x + 2 = (T x + 1) + 1 by omega, Function.iterate_succ_apply',
    iterate_running init advance halt answer T hbefore x (T x) le_rfl,
    step_running, hafter]
  rfl

theorem iterate_answer (init advance : List Bool → List Bool) (halt answer : List Bool → Bool)
    (T : List Bool → ℕ)
    (hbefore : ∀ x t, t < T x → halt (advance^[t] (init x)) = false)
    (hafter : ∀ x, halt (advance^[T x] (init x)) = true) (x : List Bool) :
    (step init advance halt answer)^[T x + 3] (pair [] x) = [answer (advance^[T x] (init x))] := by
  rw [show T x + 3 = (T x + 2) + 1 by omega, Function.iterate_succ_apply',
    iterate_finished init advance halt answer T hbefore hafter, step_finished]

theorem mem_PSPACE {L : Language} {init advance : List Bool → List Bool} {halt answer : List Bool → Bool}
    (hi : init ∈ FP) (ha : advance ∈ FP)
    (hh : (fun s => [halt s]) ∈ FP) (hr : (fun s => [answer s]) ∈ FP)
    (r w : Polynomial ℕ) (T : List Bool → ℕ)
    (hlen : ∀ x t, t ≤ T x → (advance^[t] (init x)).length ≤ r.eval x.length)
    (htime : ∀ x, T x ≤ 2 ^ w.eval x.length)
    (hbefore : ∀ x t, t < T x → halt (advance^[t] (init x)) = false)
    (hafter : ∀ x, halt (advance^[T x] (init x)) = true)
    (hanswer : ∀ x, x ∈ L ↔ answer (advance^[T x] (init x)) = true) : L ∈ PSPACE := by
  refine SpaceIter.mem_PSPACE_of_iterate (step_mem_FP hi ha hh hr)
    (Polynomial.X + r + 3) (w + 2) (fun x => T x + 2) ?_ (by intro x; omega) ?_ ?_ ?_ ?_ ?_
  · intro x i hib
    have hr := hlen x (T x) le_rfl
    cases i with
    | zero => simp only [Function.iterate_zero, id_eq, pair_length, List.length_nil]
              simp; omega
    | succ k =>
        by_cases hk : k ≤ T x
        · rw [iterate_running init advance halt answer T hbefore x k hk]
          have h := hlen x k hk
          simp only [running, List.length_cons]
          simp; omega
        · have heq : k + 1 = T x + 2 ∨ k + 1 = T x + 3 := by omega
          rcases heq with heq | heq
          · rw [heq, iterate_finished init advance halt answer T hbefore hafter]
            simp only [finished, List.length_cons]
            simp; omega
          · rw [heq, iterate_answer init advance halt answer T hbefore hafter]
            simp
  · intro x
    have ht := htime x
    have hp : 0 < 2 ^ w.eval x.length := pow_pos (by decide) _
    simp only [Polynomial.eval_add, Polynomial.eval_ofNat, pow_add]
    norm_num
    omega
  · intro x i hi hib
    cases i with
    | zero => omega
    | succ k =>
        rw [iterate_running init advance halt answer T hbefore x k (by omega)]
        rfl
  · intro x
    rw [iterate_finished init advance halt answer T hbefore hafter]
    rfl
  · intro x
    rw [show (T x + 2) + 1 = T x + 3 by omega,
      iterate_answer init advance halt answer T hbefore hafter]
    simp
  · intro x
    rw [show (T x + 2) + 1 = T x + 3 by omega,
      iterate_answer init advance halt answer T hbefore hafter]
    exact hanswer x

end LeanCanny.Computation.HaltingIteration
