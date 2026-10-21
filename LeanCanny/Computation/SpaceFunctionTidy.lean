/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunction
public import LeanCanny.Computation.TidyFP
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Legacy output routines as tidy space computations

This compatibility adapter discharges the old clock and first-halt obligations
once. New compositions consume only the resulting polynomial-space certificate.
-/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction

open Turing.MultiTapeTM

def frozen {f : List Bool → List Bool} (E : SpaceFunction f) (s : List Bool) : List Bool :=
  if E.halt s then s else E.advance s

theorem frozen_iterate {f : List Bool → List Bool} (E : SpaceFunction f) (x : List Bool) (t : ℕ) :
    E.frozen^[t] (E.init x) = E.advance^[min t (E.time x)] (E.init x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases ht : t < E.time x
    · rw [Nat.min_eq_left ht.le, Nat.min_eq_left (Nat.succ_le_of_lt ht)]
      simp only [frozen, E.before x t ht, Bool.false_eq_true, ↓reduceIte,
        Function.iterate_succ_apply']
    · have hT : E.time x ≤ t := Nat.le_of_not_gt ht
      rw [Nat.min_eq_right hT, Nat.min_eq_right (hT.trans (Nat.le_succ t))]
      simp only [frozen, E.after, ↓reduceIte]

theorem computable {f : List Bool → List Bool} (E : SpaceFunction f) :
    ComputableTidilyInPolySpace f encBits encBits := by
  have hlength : ComputableTidilyInPolyTime List.length encBits encUnary :=
    ComputableTidilyInPolyTime.length encBool
  have hcount := ComputableTidilyInPolyTime.binary_two_pow.comp
    ((ComputableTidilyInPolyTime.unary_eval E.clock).comp hlength)
  have hinit := ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_mem_FP E.initFP)
  have hstep : ComputableTidilyInPolySpace E.frozen encBits encBits :=
    (ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_flag E.haltFP)).ite
      ComputableTidilyInPolySpace.id'
      (ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_mem_FP E.advanceFP))
  have h := ComputableTidilyInPolySpace.iterate hcount hinit hstep
    (B := fun x => E.space.eval x.length)
    (PolyBounded.of_polynomiallyBounded _ (.polynomial_eval E.space)) (fun x k _ => by
      rw [frozen_iterate]
      exact E.length_le x _ (Nat.min_le_right _ _))
  refine ((ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_mem_FP E.outputFP)).comp h).congr
    fun x => ?_
  simp only [Function.comp_apply]
  rw [frozen_iterate, Nat.min_eq_right (E.time_le x), E.correct]

end LeanCanny.Computation.SpaceFunction
