/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimePairing
public import LeanCanny.Computation.PolyTimeBounds
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration

/-! # Native polynomial-time loops and right folds

Unary-counted loops and right folds use the native iteration and fold rules.
Callers supply only mathematical accumulator bounds; no execution clock or
clamped evaluator is needed.
-/

@[expose] public section

namespace LeanCanny

open Turing.MultiTapeTM

theorem iterate_mem_FP {F init ruler width : List Bool → List Bool}
    (hF : F ∈ FP) (hinit : init ∈ FP) (hruler : ruler ∈ FP) (hwidth : width ∈ FP)
    (hbound : ∀ z, ∀ n ≤ (ruler z).length,
      (F^[n] (init z)).length ≤ (width z).length) :
    (fun z => F^[(ruler z).length] (init z)) ∈ FP := by
  exact ComputableTidilyInPolyTime.iterate
    (ComputableTidilyInPolyTime.length_bits.comp hruler) hinit hF
    hwidth.polyBounded_length hbound

theorem iterate_mem_FP_of_polyBound {F init ruler : List Bool → List Bool}
    (hF : F ∈ FP) (hinit : init ∈ FP) (hruler : ruler ∈ FP) {B : ℕ → ℕ}
    (hB : PolyBound B)
    (hbound : ∀ z, ∀ n ≤ (ruler z).length, (F^[n] (init z)).length ≤ B z.length) :
    (fun z => F^[(ruler z).length] (init z)) ∈ FP := by
  exact ComputableTidilyInPolyTime.iterate
    (ComputableTidilyInPolyTime.length_bits.comp hruler) hinit hF
    (hB.polyBounded (fun z : List Bool => z.length)) hbound

theorem iterate_length_le_of_step_le {F : List Bool → List Bool} {x : List Bool}
    {N c : ℕ} (hstep : ∀ n < N, (F^[n + 1] x).length ≤ (F^[n] x).length + c) :
    ∀ m ≤ N, (F^[m] x).length ≤ x.length + c * m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    have := hstep m (by omega)
    have := ih (by omega)
    rw [Nat.mul_succ]
    omega

theorem iterate_mem_FP_of_step_le {F init ruler : List Bool → List Bool}
    (hF : F ∈ FP) (hinit : init ∈ FP) (hruler : ruler ∈ FP) (c : ℕ)
    (hstep : ∀ z, ∀ n < (ruler z).length,
      (F^[n + 1] (init z)).length ≤ (F^[n] (init z)).length + c) :
    (fun z => F^[(ruler z).length] (init z)) ∈ FP := by
  apply ComputableTidilyInPolyTime.iterate
    (ComputableTidilyInPolyTime.length_bits.comp hruler) hinit hF
    (hinit.polyBounded_length.add ((PolyBounded.const c).mul hruler.polyBounded_length))
  intro z n hn
  exact (iterate_length_le_of_step_le (hstep z) n hn).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left c hn) _)

theorem recFold_mem_FP_of_bound {A B E w s : List Bool → List Bool}
    {g : List Bool → List Bool → List Bool}
    (hA : A ∈ FP) (hB : B ∈ FP) (hE : E ∈ FP) (hw : w ∈ FP) (hs : s ∈ FP)
    (hnil : ∀ z, g z [] = E z)
    (hfalse : ∀ z t, g z (false :: t) = A (pair (pair (w z) (g z t)) t))
    (htrue : ∀ z t, g z (true :: t) = B (pair (pair (w z) (g z t)) t))
    {bound : ℕ → ℕ} (hbound : PolyBound bound)
    (hle : ∀ z t, t <:+ s z → (g z t).length ≤ bound z.length) :
    (fun z => g z (s z)) ∈ FP := by
  let step := fun (par : List Bool) (state : List Bool × List Bool) (b : Bool) =>
    (if b then B (pair (pair par state.1) state.2)
      else A (pair (pair par state.1) state.2), b :: state.2)
  have hstep : ComputableTidilyInPolyTime
      (fun p : (List Bool × (List Bool × List Bool)) × Bool => step p.1.1 p.1.2 p.2)
      (encPair (encPair encBits (encPair encBits encBits)) encBool)
      (encPair encBits encBits) := by
    dsimp [step]
    apply ComputableTidilyInPolyTime.prod
    · apply ComputableTidilyInPolyTime.cond
      · fun_prop
      · exact hB.comp (by fun_prop)
      · exact hA.comp (by fun_prop)
    · fun_prop
  have h := ComputableTidilyInPolyTime.foldlWith_spec
    (encA := encBool) (encL := encBits) (encB := encPair encBits encBits)
    (step := step) hw (mem_FP_comp hs reverse_mem_FP)
    (hE.prod (ComputableTidilyInPolyTime.const [])) hstep
    (fun z consumed state => state = (g z consumed.reverse, consumed.reverse))
    (fun z => by simp [hnil])
    (fun z consumed state b _ hstate => by
      subst state
      cases b <;> simp [step, hfalse, htrue])
    (((PolyBounded.const 2).mul (hbound.polyBounded (fun z : List Bool => z.length))).add
      (hs.polyBounded_length.add (PolyBounded.const 1)))
    (fun z consumed state hprefix hstate => by
      subst state
      have hsuffix : consumed.reverse <:+ s z := by
        obtain ⟨tail, ht⟩ := hprefix
        refine ⟨tail.reverse, ?_⟩
        simpa only [List.reverse_append, List.reverse_reverse, Function.comp_apply]
          using congrArg List.reverse ht
      have hb := hle z _ hsuffix
      have hl := hsuffix.length_le
      simp only [List.length_reverse] at hl
      simp only [length_encPair, encBits_apply, List.length_reverse]
      omega)
  have hresult := h.1.fst'
  have hcorrect := h.2
  refine mem_FP_of_eq hresult fun z => ?_
  simpa only [List.reverse_reverse, Function.comp_apply] using congrArg Prod.fst (hcorrect z)

end LeanCanny
