/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunction

/-!
# Input preparation and retention for certified output routines

FP input preparation composes the space and clock polynomials with its output
length bound. Retaining the original input in an explicit paired state adds
`2*input.length+2` bits and preserves the child's exact first halting time.
-/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction
open Complexity

def congr {f g : List Bool → List Bool} (E : SpaceFunction f) (h : f = g) : SpaceFunction g := h ▸ E

noncomputable def precompose {f : List Bool → List Bool} (E : SpaceFunction f)
    (g : List Bool → List Bool) (hg : g ∈ FP) : SpaceFunction (f ∘ g) := by
  let p := Classical.choose (Cobham.output_length_poly_of_mem_FP hg)
  have hp : ∀ x, (g x).length ≤ p.eval x.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hg)
  refine { init := E.init ∘ g
           advance := E.advance
           halt := E.halt
           output := E.output
           initFP := mem_FP_comp hg E.initFP
           advanceFP := E.advanceFP
           haltFP := E.haltFP
           outputFP := E.outputFP
           space := E.space.comp p
           clock := E.clock.comp p
           time := E.time ∘ g
           length_le := ?_
           time_le := ?_
           before := fun x => E.before (g x)
           after := fun x => E.after (g x)
           correct := fun x => E.correct (g x) }
  · intro x t ht
    have h := (E.length_le (g x) t ht).trans (polynomial_eval_mono_nat E.space (hp x))
    simpa only [Polynomial.eval_comp, Function.comp_apply] using h
  · intro x
    have h := (E.time_le (g x)).trans
      (Nat.pow_le_pow_right (by decide) (polynomial_eval_mono_nat E.clock (hp x)))
    simpa only [Polynomial.eval_comp, Function.comp_apply] using h

def retainStep (advance : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pairFst p) (advance (pairSnd p))

def retainOutput (output : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pairFst p) (output (pairSnd p))

theorem retainStep_mem_FP {advance : List Bool → List Bool} (ha : advance ∈ FP) :
    retainStep advance ∈ FP := mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP ha)

theorem retainOutput_mem_FP {output : List Bool → List Bool} (ho : output ∈ FP) :
    retainOutput output ∈ FP := mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP ho)

theorem retain_iterate (advance : List Bool → List Bool) (x s : List Bool) (t : ℕ) :
    (retainStep advance)^[t] (pair x s) = pair x (advance^[t] s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [retainStep, pairFst_pair, pairSnd_pair, Function.iterate_succ_apply']

noncomputable def withInput {f : List Bool → List Bool} (E : SpaceFunction f) :
    SpaceFunction (fun x => pair x (f x)) := by
  have hi := mem_FP_pair id_mem_FP E.initFP
  have hh := mem_FP_comp pairSnd_mem_FP E.haltFP
  refine { init := fun x => pair x (E.init x)
           advance := retainStep E.advance
           halt := fun p => E.halt (pairSnd p)
           output := retainOutput E.output
           initFP := hi
           advanceFP := retainStep_mem_FP E.advanceFP
           haltFP := hh
           outputFP := retainOutput_mem_FP E.outputFP
           space := 2 * Polynomial.X + 2 + E.space
           clock := E.clock
           time := E.time
           length_le := ?_
           time_le := E.time_le
           before := ?_
           after := ?_
           correct := ?_ }
  · intro x t ht
    rw [retain_iterate, pair_length]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X] using
      Nat.add_le_add_left (E.length_le x t ht) (2 * x.length + 2)
  · intro x t ht
    rw [retain_iterate, pairSnd_pair]
    exact E.before x t ht
  · intro x
    rw [retain_iterate, pairSnd_pair]
    exact E.after x
  · intro x
    rw [retain_iterate]
    simp only [retainOutput, pairFst_pair, pairSnd_pair, E.correct]

end LeanCanny.Computation.SpaceFunction
