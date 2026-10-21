/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.RecursiveStackPotential

/-! # Encoded storage of the recursive evaluator

Strictly decreasing call ranks bound stack depth. Frame and result bounds are
required only on the input's valid frames, independently of local running times.
-/

@[expose] public section

namespace LeanCanny.Computation.RecursiveStack
open Turing.MultiTapeTM

abbrev encAction {F : Type} (encF : F ↪ List Bool) : Action F ↪ List Bool :=
  encPair encBool (encPair encBool (encPair encBits encF))

abbrev encState {F : Type} (encF : F ↪ List Bool) : State F ↪ List Bool :=
  encPair encBool (encPair encBits (encPair encF (encList encF)))

theorem Chain.frames_valid {F : Type} {localStep : F → Action F} {value : F → List Bool}
    {rank : F → ℕ} {valid : F → Prop} {a : List Bool} {r : ℕ} {stack : List F}
    (h : Chain localStep value rank valid a r stack) : ∀ p ∈ stack, valid p := by
  induction stack generalizing a r with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons parent rest ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact ih h.2.2.2.2.2 p hp

theorem Chain.depth {F : Type} {localStep : F → Action F} {value : F → List Bool}
    {rank : F → ℕ} {valid : F → Prop} {a : List Bool} {r R : ℕ} {stack : List F}
    (h : Chain localStep value rank valid a r stack) (hr : r ≤ R)
    (hb : ∀ p, valid p → rank p ≤ R) : stack.length + r ≤ R := by
  induction stack generalizing a r with
  | nil => simpa only [List.length_nil, Nat.zero_add] using hr
  | cons parent rest ih =>
    have ht := ih h.2.2.2.2.2 (hb parent h.1)
    have hl := h.2.2.2.2.1
    simp only [List.length_cons]
    omega

theorem output_length_step {F : Type} {localStep : F → Action F} {receive : F × List Bool → F}
    {value : F → List Bool} {rank fuel : F → ℕ} {valid : F → Prop} {N B : ℕ}
    (rules : Rules localStep receive value rank fuel valid N)
    (hb : ∀ p, valid p → (value p).length ≤ B) (s : State F)
    (hs : Good localStep value rank valid s) (ho : s.2.1.length ≤ B) :
    (step localStep receive s).2.1.length ≤ B := by
  rcases s with ⟨halted, output, current, stack⟩
  cases halted with
  | true => exact ho
  | false =>
    by_cases hd : (localStep current).1 = true
    · have ha := rules.done current hs.1 hd
      cases stack <;> simp only [step, Bool.false_eq_true, ite_false, ite_eq_left hd, ha, List.length_nil]
      · exact hb current hs.1
      · exact Nat.zero_le _
    · have hd' : (localStep current).1 = false := Bool.eq_false_iff.mpr hd
      by_cases hc : (localStep current).2.1 = true
      · simp only [step, hd', hc, Bool.false_eq_true, ite_false, ite_true, List.length_nil, Nat.zero_le]
      · have hc' : (localStep current).2.1 = false := Bool.eq_false_iff.mpr hc
        simp only [step, hd', hc', Bool.false_eq_true, ite_false, List.length_nil, Nat.zero_le]

theorem output_length_iterate {F : Type} {localStep : F → Action F} {receive : F × List Bool → F}
    {value : F → List Bool} {rank fuel : F → ℕ} {valid : F → Prop} {N B : ℕ}
    (rules : Rules localStep receive value rank fuel valid N)
    (hb : ∀ p, valid p → (value p).length ≤ B) (s : F) (hs : valid s) (k : ℕ) :
    ((step localStep receive)^[k] (initial s)).2.1.length ≤ B := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact output_length_step rules hb _ (good_iterate rules _ (good_initial _ _ _ _ s hs) k) ih

private theorem list_length_bound {F : Type} (encF : F ↪ List Bool) (stack : List F) (B : ℕ)
    (hb : ∀ p ∈ stack, (encF p).length ≤ B) :
    (encList encF stack).length ≤ stack.length * (2 * B + 1) := by
  rw [length_encList]
  induction stack with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons parent rest ih =>
    have hp := hb parent List.mem_cons_self
    have ht := ih fun p hp => hb p (List.mem_cons_of_mem _ hp)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem encoded_length_bound {F : Type} (encF : F ↪ List Bool)
    {localStep : F → Action F} {value : F → List Bool} {rank : F → ℕ} {valid : F → Prop}
    {R B : ℕ} (hr : ∀ p, valid p → rank p ≤ R)
    (hb : ∀ p, valid p → (encF p).length ≤ B) (s : State F)
    (hs : Good localStep value rank valid s) (ho : s.2.1.length ≤ B) :
    (encState encF s).length ≤ 5 + 4 * B + R * (2 * B + 1) := by
  have hf := hb _ hs.1
  have hl : s.2.2.2.length ≤ R := by
    cases hh : s.1 with
    | true =>
      have he : s.2.2.2 = [] := by simpa only [hh, ite_true] using hs.2
      simp only [he, List.length_nil, Nat.zero_le]
    | false =>
      have hc : Chain localStep value rank valid (value s.2.2.1) (rank s.2.2.1) s.2.2.2 := by
        simpa only [hh, Bool.false_eq_true, ite_false] using hs.2
      have hd := hc.depth (hr _ hs.1) hr
      omega
  have hb' : ∀ p ∈ s.2.2.2, (encF p).length ≤ B := by
    cases hh : s.1 with
    | true =>
      have he : s.2.2.2 = [] := by simpa only [hh, ite_true] using hs.2
      simp only [he, List.not_mem_nil, false_implies, implies_true]
    | false =>
      have hc : Chain localStep value rank valid (value s.2.2.1) (rank s.2.2.1) s.2.2.2 := by
        simpa only [hh, Bool.false_eq_true, ite_false] using hs.2
      exact fun p hp => hb p (hc.frames_valid p hp)
  have hlist := (list_length_bound encF s.2.2.2 B hb').trans (Nat.mul_le_mul_right _ hl)
  simp only [encState, length_encPair, encBool_apply, List.length_singleton, encBits_apply]
  omega

end LeanCanny.Computation.RecursiveStack
