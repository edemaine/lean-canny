/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimePairing
public import LeanCanny.Computation.PolyTimeBounds

/-! # Native polynomial-time loops and right folds

The legacy raw packet interface is implemented by typed native folds. Only the
mathematical accumulator bound remains; no execution clock or clamped evaluator
is needed.
-/

@[expose] public section

namespace LeanCanny

open Turing.MultiTapeTM

theorem iterate_mem_FP {F init ruler width : List Bool → List Bool}
    (hF : F ∈ FP) (hinit : init ∈ FP) (hruler : ruler ∈ FP) (hwidth : width ∈ FP)
    (hbound : ∀ z, ∀ n ≤ (ruler z).length,
      (F^[n] (init z)).length ≤ (width z).length) :
    (fun z => F^[(ruler z).length] (init z)) ∈ FP := by
  have h := ComputableTidilyInPolyTime.foldl' (encA := encBool) (encL := encBits)
    (step := fun state _ => F state) hruler hinit
    (hF.comp (ComputableTidilyInPolyTime.fst encBits encBool)) hwidth.polyBounded_length
    (fun z i _ => by
      simpa only [List.foldl_const, List.length_take, encBits_apply] using
        hbound z (min i (ruler z).length) (Nat.min_le_right _ _))
  change ComputableTidilyInPolyTime _ encBits encBits
  simpa only [List.foldl_const] using h

theorem iterate_mem_FP_of_polyBound {F init ruler : List Bool → List Bool}
    (hF : F ∈ FP) (hinit : init ∈ FP) (hruler : ruler ∈ FP) {B : ℕ → ℕ}
    (hB : PolyBound B)
    (hbound : ∀ z, ∀ n ≤ (ruler z).length, (F^[n] (init z)).length ≤ B z.length) :
    (fun z => F^[(ruler z).length] (init z)) ∈ FP := by
  have h := ComputableTidilyInPolyTime.foldl' (encA := encBool) (encL := encBits)
    (step := fun state _ => F state) hruler hinit
    (hF.comp (ComputableTidilyInPolyTime.fst encBits encBool))
    (hB.polyBounded (fun z : List Bool => z.length))
    (fun z i _ => by
      simpa only [List.foldl_const, List.length_take, encBits_apply] using
        hbound z (min i (ruler z).length) (Nat.min_le_right _ _))
  change ComputableTidilyInPolyTime _ encBits encBits
  simpa only [List.foldl_const] using h

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
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP hinit
  obtain ⟨q, hq⟩ := output_length_poly_of_mem_FP hruler
  refine iterate_mem_FP_of_polyBound hF hinit hruler
    ((PolyBound.eval p).add ((PolyBound.const c).mul (PolyBound.eval q))) fun z n hn => ?_
  have h := iterate_length_le_of_step_le (hstep z) n hn
  have h' := Nat.mul_le_mul_left c (hn.trans (hq z))
  exact h.trans (Nat.add_le_add (hp z) h')

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
