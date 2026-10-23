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

/-- A typed right fold over raw bits. Suffix invariants are transported to
prefix invariants of the reversed word for the upstream native left fold. -/
theorem foldrWith_spec {γ β π : Type} {encIn : γ ↪ List Bool}
    {encB : β ↪ List Bool} {encP : π ↪ List Bool}
    {par : γ → π} {list : γ → List Bool} {init : γ → β}
    {step : π → β → Bool → β}
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn encBits)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : (π × β) × Bool => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encBool) encB)
    (invariant : γ → List Bool → β → Prop)
    (hbase : ∀ x, invariant x [] (init x))
    (hpreserve : ∀ x tail state bit, bit :: tail <:+ list x →
      invariant x tail state → invariant x (bit :: tail) (step (par x) state bit))
    {size : γ → ℕ} (hsize : PolyBounded (fun x => (encIn x).length) size)
    (hbound : ∀ x tail state, tail <:+ list x → invariant x tail state →
      (encB state).length ≤ size x) :
    ComputableTidilyInPolyTime
      (fun x => (list x).foldr (fun bit state => step (par x) state bit) (init x)) encIn encB ∧
      ∀ x, invariant x (list x)
        ((list x).foldr (fun bit state => step (par x) state bit) (init x)) := by
  have hsuffix (x : γ) (consumed : List Bool) (hp : consumed <+: (list x).reverse) :
      consumed.reverse <:+ list x := by
    obtain ⟨tail, ht⟩ := hp
    refine ⟨tail.reverse, ?_⟩
    simpa only [List.reverse_append, List.reverse_reverse] using congrArg List.reverse ht
  have h := ComputableTidilyInPolyTime.foldlWith_spec
    (encA := encBool) (encL := encBits) hpar
    (ComputableTidilyInPolyTime.bitsReverse.comp hlist) hinit hstep
    (fun x consumed state => invariant x consumed.reverse state) hbase
    (fun x consumed state bit hp hi => by
      have ht := hsuffix x (consumed ++ [bit]) hp
      simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append]
        using hpreserve x consumed.reverse state bit
          (by simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append] using ht) hi)
    hsize (fun x consumed state hp hi => hbound x _ state (hsuffix x consumed hp) hi)
  simpa only [List.foldl_reverse, List.reverse_reverse, Function.comp_apply] using h

/-- Right-fold recursion with an arbitrary mathematical state code. The code
need not be injective and no decoder is required. Only reachable suffix states
need a length bound. -/
theorem foldrEncodedWith_spec {γ σ π : Type} {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool} (code : σ → List Bool)
    {par : γ → π} {list : γ → List Bool} {g : γ → List Bool → σ}
    {step : π → List Bool → Bool → List Bool}
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn encBits)
    (hinit : ComputableTidilyInPolyTime (fun x => code (g x [])) encIn encBits)
    (hstep : ComputableTidilyInPolyTime (fun p : (π × List Bool) × Bool => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encBits) encBool) encBits)
    (hcons : ∀ x tail bit, step (par x) (code (g x tail)) bit = code (g x (bit :: tail)))
    {size : γ → ℕ} (hsize : PolyBounded (fun x => (encIn x).length) size)
    (hbound : ∀ x tail, tail <:+ list x → (code (g x tail)).length ≤ size x) :
    ComputableTidilyInPolyTime (fun x => code (g x (list x))) encIn encBits := by
  have h := foldrWith_spec hpar hlist hinit hstep
    (fun x tail state => state = code (g x tail)) (fun _ => rfl)
    (fun x tail state bit _ hs => by subst state; exact hcons x tail bit)
    hsize (fun x tail state ht hs => by subst state; exact hbound x tail ht)
  exact h.1.of_enc_eq fun x => by simpa only [encBits_apply] using (h.2 x).symm

/-- Suffix-aware right recursion. The native fold stores both the accumulator
and the already processed tail; both contribute to its polynomial bound. -/
theorem paraWith_spec {γ β π : Type} {encIn : γ ↪ List Bool}
    {encB : β ↪ List Bool} {encP : π ↪ List Bool}
    {par : γ → π} {list : γ → List Bool} {init : γ → β}
    {step : π → β → List Bool → Bool → β}
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn encBits)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime
      (fun p : (π × (β × List Bool)) × Bool => step p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair encP (encPair encB encBits)) encBool) encB)
    (invariant : γ → List Bool → β → Prop)
    (hbase : ∀ x, invariant x [] (init x))
    (hpreserve : ∀ x tail state bit, bit :: tail <:+ list x →
      invariant x tail state → invariant x (bit :: tail) (step (par x) state tail bit))
    {size : γ → ℕ} (hsize : PolyBounded (fun x => (encIn x).length) size)
    (hbound : ∀ x tail state, tail <:+ list x → invariant x tail state →
      (encB state).length ≤ size x) :
    ComputableTidilyInPolyTime
      (fun x => ((list x).foldr (fun bit state =>
        (step (par x) state.1 state.2 bit, bit :: state.2)) (init x, [])).1) encIn encB ∧
      ∀ x, invariant x (list x)
        (((list x).foldr (fun bit state =>
          (step (par x) state.1 state.2 bit, bit :: state.2)) (init x, [])).1) := by
  have hpair : ComputableTidilyInPolyTime
      (fun p : (π × (β × List Bool)) × Bool =>
        (step p.1.1 p.1.2.1 p.1.2.2 p.2, p.2 :: p.1.2.2))
      (encPair (encPair encP (encPair encB encBits)) encBool) (encPair encB encBits) := by
    apply ComputableTidilyInPolyTime.prod hstep
    fun_prop
  have h := foldrWith_spec (encB := encPair encB encBits) (encP := encP)
    (step := fun par (state : β × List Bool) bit =>
      (step par state.1 state.2 bit, bit :: state.2))
    hpar hlist (hinit.prod (ComputableTidilyInPolyTime.const [])) hpair
    (fun x tail state => invariant x tail state.1 ∧ state.2 = tail)
    (fun x => ⟨hbase x, rfl⟩)
    (fun x tail state bit ht hs => by
      exact ⟨by simpa only [hs.2] using hpreserve x tail state.1 bit ht hs.1,
        by simp only [hs.2]⟩)
    (((PolyBounded.const 2).mul hsize).add
      (hlist.polyBounded_length.add (PolyBounded.const 1)))
    (fun x tail state ht hs => by
      have hb := hbound x tail state.1 ht hs.1
      have hl := ht.length_le
      simp only [length_encPair, encBits_apply, hs.2]
      omega)
  exact ⟨h.1.fst', fun x => (h.2 x).1⟩

/-- Suffix-aware recursion for existing wire formats, without a state decoder
or an injectivity requirement on the mathematical state's code. -/
theorem paraEncodedWith_spec {γ σ π : Type} {encIn : γ ↪ List Bool}
    {encP : π ↪ List Bool} (code : σ → List Bool)
    {par : γ → π} {list : γ → List Bool} {g : γ → List Bool → σ}
    {step : π → List Bool → List Bool → Bool → List Bool}
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn encBits)
    (hinit : ComputableTidilyInPolyTime (fun x => code (g x [])) encIn encBits)
    (hstep : ComputableTidilyInPolyTime
      (fun p : (π × (List Bool × List Bool)) × Bool => step p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair encP (encPair encBits encBits)) encBool) encBits)
    (hcons : ∀ x tail bit, step (par x) (code (g x tail)) tail bit = code (g x (bit :: tail)))
    {size : γ → ℕ} (hsize : PolyBounded (fun x => (encIn x).length) size)
    (hbound : ∀ x tail, tail <:+ list x → (code (g x tail)).length ≤ size x) :
    ComputableTidilyInPolyTime (fun x => code (g x (list x))) encIn encBits := by
  have h := paraWith_spec hpar hlist hinit hstep
    (fun x tail state => state = code (g x tail)) (fun _ => rfl)
    (fun x tail state bit _ hs => by subst state; exact hcons x tail bit)
    hsize (fun x tail state ht hs => by subst state; exact hbound x tail ht)
  exact h.1.of_enc_eq fun x => by simpa only [encBits_apply] using (h.2 x).symm

theorem recFold_mem_FP_of_bound {A B E w s : List Bool → List Bool}
    {g : List Bool → List Bool → List Bool}
    (hA : A ∈ FP) (hB : B ∈ FP) (hE : E ∈ FP) (hw : w ∈ FP) (hs : s ∈ FP)
    (hnil : ∀ z, g z [] = E z)
    (hfalse : ∀ z t, g z (false :: t) = A (pair (pair (w z) (g z t)) t))
    (htrue : ∀ z t, g z (true :: t) = B (pair (pair (w z) (g z t)) t))
    {bound : ℕ → ℕ} (hbound : PolyBound bound)
    (hle : ∀ z t, t <:+ s z → (g z t).length ≤ bound z.length) :
    (fun z => g z (s z)) ∈ FP := by
  let step := fun (par state tail : List Bool) (bit : Bool) =>
    if bit then B (pair (pair par state) tail) else A (pair (pair par state) tail)
  have hstep : ComputableTidilyInPolyTime
      (fun p : (List Bool × (List Bool × List Bool)) × Bool =>
        step p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair encBits (encPair encBits encBits)) encBool) encBits := by
    dsimp [step]
    apply ComputableTidilyInPolyTime.cond
    · fun_prop
    · exact hB.comp (by fun_prop)
    · exact hA.comp (by fun_prop)
  exact paraEncodedWith_spec id hw hs
    (hE.of_enc_eq fun z => hnil z) hstep
    (fun z tail bit => by
      cases bit <;> simp only [step, hfalse, htrue, id_eq, Bool.false_eq_true, ↓reduceIte])
    (hbound.polyBounded (fun z : List Bool => z.length)) hle

end LeanCanny
