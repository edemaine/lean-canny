/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledFeasibilityFunction

/-! # One fixed counting-level decision for a bounded word and two existential tests -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped Classical

theorem bounded_two_test_decision_mem {α : Type} {n m : α × List Bool → ℕ}
    {enc : α ↪ List Bool} {a : ℕ}
    {P : (q : α × List Bool) → MvPolynomial (Fin (n q)) ℤ}
    {Q : (q : α × List Bool) → MvPolynomial (Fin (m q)) ℤ}
    (CP : Controlled P (encPair enc encBits) a) (CQ : Controlled Q (encPair enc encBits) a)
    (E : Decoder enc) (width : α → ℕ) (hw : ComputableInPolyTime width enc encUnary) :
    {w | ∃ word : List Bool, word.length = width w ∧
      (∃ x : Fin (n (w, word)) → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (P (w, word)) = 0) ∧
      ¬∃ y : Fin (m (w, word)) → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) y (Q (w, word)) = 0} ∈
        CountingLevel (a + 27) enc := by
  have hp := CP.feasibilityFunction_mem (Decoder.pair E Decoder.bits)
  have hq := CQ.feasibilityFunction_mem (Decoder.pair E Decoder.bits)
  have hbool : ComputableInPolyTime (fun t : Bool × Bool => t.1 && !t.2) (encPair encBool encBool) encBool := by fun_prop
  have htest := CountingFunction.map (CountingFunction.prod hp hq) hbool
  have hword := CountingFunction.exists_bits E htest hw
  have hlevel := CountingFunction.decision hword
  simpa only [MvPolynomial.eval_map, Function.comp_def, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, Nat.add_assoc] using hlevel

end LeanCanny.CountingHierarchy
