/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionComposition

/-!
# FP-controlled branches between certified space routines

A single tag selects a child for the entire run. Both branches have complete
state/clock certificates; summing their resource polynomials bounds the selected
run. Immediate FP outputs have a zero-transition certificate.
-/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction
open Complexity

noncomputable def ofFP (f : List Bool → List Bool) (hf : f ∈ FP) : SpaceFunction f := by
  let p := Classical.choose (Cobham.output_length_poly_of_mem_FP hf)
  have hp : ∀ x, (f x).length ≤ p.eval x.length := Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hf)
  refine { init := f
           advance := id
           halt := fun _ => true
           output := id
           initFP := hf
           advanceFP := id_mem_FP
           haltFP := constFn_mem_FP [true]
           outputFP := id_mem_FP
           space := p
           clock := 0
           time := fun _ => 0
           length_le := ?_
           time_le := fun _ => Nat.zero_le _
           before := ?_
           after := fun _ => rfl
           correct := fun _ => rfl }
  · intro x t ht
    have ht0 : t = 0 := by omega
    simpa only [ht0, Function.iterate_zero, id_eq] using hp x
  · intro x t ht
    omega

def branchInit (pred : List Bool → Bool) (left right : List Bool → List Bool) (x : List Bool) : List Bool :=
  if pred x then false :: left x else true :: right x

def branchStep (left right : List Bool → List Bool) (p : List Bool) : List Bool :=
  if p[0]?.getD false then true :: right (p.drop 1) else false :: left (p.drop 1)

def branchHalt (left right : List Bool → Bool) (p : List Bool) : Bool :=
  if p[0]?.getD false then right (p.drop 1) else left (p.drop 1)

def branchOutput (left right : List Bool → List Bool) (p : List Bool) : List Bool :=
  if p[0]?.getD false then right (p.drop 1) else left (p.drop 1)

theorem branchInit_mem_FP {pred : List Bool → Bool} {left right : List Bool → List Bool}
    (hp : (fun x => [pred x]) ∈ FP) (hl : left ∈ FP) (hr : right ∈ FP) : branchInit pred left right ∈ FP := by
  have h := (FPPred.of_flag hp).ite_mem_FP (mem_FP_comp hl (Cobham.cons_mem_FP false))
    (mem_FP_comp hr (Cobham.cons_mem_FP true))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem branchStep_mem_FP {left right : List Bool → List Bool} (hl : left ∈ FP) (hr : right ∈ FP) :
    branchStep left right ∈ FP := by
  have hd := drop_mem_FP id_mem_FP (UnaryFn.const 1)
  have h := (FPPred.getBit id_mem_FP (UnaryFn.const 0)).ite_mem_FP
    (mem_FP_comp (mem_FP_comp hd hr) (Cobham.cons_mem_FP true))
    (mem_FP_comp (mem_FP_comp hd hl) (Cobham.cons_mem_FP false))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem branchHalt_mem_FP {left right : List Bool → Bool}
    (hl : (fun p => [left p]) ∈ FP) (hr : (fun p => [right p]) ∈ FP) :
    (fun p => [branchHalt left right p]) ∈ FP := by
  have hd := drop_mem_FP id_mem_FP (UnaryFn.const 1)
  have h := (FPPred.getBit id_mem_FP (UnaryFn.const 0)).ite_mem_FP (mem_FP_comp hd hr) (mem_FP_comp hd hl)
  refine mem_FP_of_eq (g := fun p => [branchHalt left right p]) h ?_
  intro p
  cases hp : p[0]?.getD false <;> simp [branchHalt, Function.comp_apply, hp]

theorem branchOutput_mem_FP {left right : List Bool → List Bool} (hl : left ∈ FP) (hr : right ∈ FP) :
    branchOutput left right ∈ FP := by
  have hd := drop_mem_FP id_mem_FP (UnaryFn.const 1)
  have h := (FPPred.getBit id_mem_FP (UnaryFn.const 0)).ite_mem_FP (mem_FP_comp hd hr) (mem_FP_comp hd hl)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem iterate_left (left right : List Bool → List Bool) (s : List Bool) (t : ℕ) :
    (branchStep left right)^[t] (false :: s) = false :: left^[t] s := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [branchStep, Function.iterate_succ_apply']

theorem iterate_right (left right : List Bool → List Bool) (s : List Bool) (t : ℕ) :
    (branchStep left right)^[t] (true :: s) = true :: right^[t] s := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [branchStep, Function.iterate_succ_apply']

noncomputable def branch {f g : List Bool → List Bool} (pred : List Bool → Bool)
    (hp : (fun x => [pred x]) ∈ FP) (L : SpaceFunction f) (R : SpaceFunction g) :
    SpaceFunction (fun x => if pred x then f x else g x) := by
  refine { init := branchInit pred L.init R.init
           advance := branchStep L.advance R.advance
           halt := branchHalt L.halt R.halt
           output := branchOutput L.output R.output
           initFP := branchInit_mem_FP hp L.initFP R.initFP
           advanceFP := branchStep_mem_FP L.advanceFP R.advanceFP
           haltFP := branchHalt_mem_FP L.haltFP R.haltFP
           outputFP := branchOutput_mem_FP L.outputFP R.outputFP
           space := 1 + L.space + R.space
           clock := L.clock + R.clock
           time := fun x => if pred x then L.time x else R.time x
           length_le := ?_
           time_le := ?_
           before := ?_
           after := ?_
           correct := ?_ }
  · intro x t ht
    cases h : pred x with
    | false =>
      simp only [h, Bool.false_eq_true, ↓reduceIte] at ht
      simp only [branchInit, h, Bool.false_eq_true, ↓reduceIte, iterate_right]
      have hl := R.length_le x t ht
      simp only [List.length_cons, Polynomial.eval_add, Polynomial.eval_one]
      omega
    | true =>
      simp only [h, ↓reduceIte] at ht
      simp only [branchInit, h, ↓reduceIte, iterate_left]
      have hl := L.length_le x t ht
      simp only [List.length_cons, Polynomial.eval_add, Polynomial.eval_one]
      omega
  · intro x
    cases h : pred x with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Polynomial.eval_add]
      exact (R.time_le x).trans (Nat.pow_le_pow_right (by decide) (by omega))
    | true =>
      simp only [↓reduceIte, Polynomial.eval_add]
      exact (L.time_le x).trans (Nat.pow_le_pow_right (by decide) (by omega))
  · intro x t ht
    cases h : pred x with
    | false =>
      simp only [h, Bool.false_eq_true, ↓reduceIte] at ht
      simpa [branchInit, h, iterate_right, branchHalt] using R.before x t ht
    | true =>
      simp only [h, ↓reduceIte] at ht
      simpa [branchInit, h, iterate_left, branchHalt] using L.before x t ht
  · intro x
    cases h : pred x with
    | false => simpa [branchInit, h, iterate_right, branchHalt] using R.after x
    | true => simpa [branchInit, h, iterate_left, branchHalt] using L.after x
  · intro x
    cases h : pred x with
    | false => simpa [branchInit, h, iterate_right, branchOutput] using R.correct x
    | true => simpa [branchInit, h, iterate_left, branchOutput] using L.correct x

end LeanCanny.Computation.SpaceFunction
