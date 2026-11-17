/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledFeasibility

/-! # A constructed Boolean function for real feasibility -/

public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped Classical

variable {α : Type} {n : α → ℕ} {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
  {enc : α ↪ List Bool} {a : ℕ}

/-- The actual feasibility Boolean function is available one function level
before its counting-level language decision. This supports same-level Boolean
combinations of a fixed number of existential queries. -/
theorem feasibilityFunction_mem (C : Controlled P enc a) (E : Decoder enc) :
    (fun w => decide (∃ x : Fin (n w) → ℝ, eval x ((P w).map (Int.castRingHom ℝ)) = 0)) ∈
      CountingFunction (a + 25) enc encBool := by
  let Q := C.mul C
  let d : α → ℕ := fun w => 2 * (Q.degreeBound w + 1)
  have hdpos (w : α) : 1 ≤ d w := by dsimp only [d]; omega
  have hdeg (w : α) : (P w * P w).totalDegree ≤ d w + 1 :=
    (Q.degree_le w).trans (by dsimp only [d]; omega)
  have heven (w : α) : Even (d w + 2) := by
    refine ⟨Q.degreeBound w + 2, ?_⟩
    dsimp only [d]
    omega
  have hd : ComputableInPolyTime d enc encNat := ComputableInPolyTime.binary_mul' (.const 2)
    (ComputableInPolyTime.binary_add' Q.degree_computable (.const 1))
  have hFn (w : α) (x : Fin (n w) → ℝ) :
      0 ≤ eval x ((P w * P w).map (Int.castRingHom ℝ)) := by
    simpa only [map_mul] using mul_self_nonneg (eval x ((P w).map (Int.castRingHom ℝ)))
  have htest := Q.normWitnessTest_mem E hdpos hdeg hd
  have hword := CountingFunction.exists_bits E htest (Q.feasibilityWitnessWidth_polyTime hd)
  have heq (w : α) : (∃ x : Fin (n w) → ℝ, eval x ((P w).map (Int.castRingHom ℝ)) = 0) ↔
      ∃ word : List Bool, word.length = Q.feasibilityWitnessWidth d w ∧ Q.normWitnessTest d hdeg (w, word) = true := by
    rw [← Q.feasibility_iff_word_witness d hdpos hdeg heven hFn w]
    simp only [map_mul, mul_self_eq_zero]
  have hfun : (fun w => decide (∃ x : Fin (n w) → ℝ, eval x ((P w).map (Int.castRingHom ℝ)) = 0)) =
      (fun w => decide (∃ word : List Bool, word.length = Q.feasibilityWitnessWidth d w ∧
        Q.normWitnessTest d hdeg (w, word) = true)) := by
    funext w
    exact congrArg (fun p : Prop => decide p) (propext (heq w))
  rw [hfun]
  simpa only [Nat.add_assoc] using hword

end LeanCanny.CountingHierarchy.Controlled
