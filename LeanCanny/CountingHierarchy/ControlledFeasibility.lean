/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledFeasibilityWitnesses
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Aggregation

/-! # Real feasibility of controlled polynomial families in C_(a+26) P -/

public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped Classical

variable {α : Type} {n : α → ℕ} {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
  {enc : α ↪ List Bool} {a : ℕ}

/-- Source evaluation, rather than expanded coefficients, suffices for a
fixed-level real-feasibility decision. The Boolean witness has polynomial
width computed solely from the primary instance. -/
theorem nonnegative_feasibility_mem (C : Controlled P enc a) (E : Decoder enc) {d : α → ℕ}
    (hdpos : ∀ w, 1 ≤ d w) (hdeg : ∀ w, (P w).totalDegree ≤ d w + 1)
    (heven : ∀ w, Even (d w + 2)) (hd : ComputableInPolyTime d enc encNat)
    (hFn : ∀ w, ∀ x : Fin (n w) → ℝ, 0 ≤ eval x ((P w).map (Int.castRingHom ℝ))) :
    {w | ∃ x : Fin (n w) → ℝ, eval x ((P w).map (Int.castRingHom ℝ)) = 0} ∈
      CountingLevel (a + 26) enc := by
  have htest := C.normWitnessTest_mem E hdpos hdeg hd
  have hdec := CountingFunction.exists_bits E htest (C.feasibilityWitnessWidth_polyTime hd)
  have hlevel : {w | ∃ word : List Bool, word.length = C.feasibilityWitnessWidth d w ∧
      C.normWitnessTest d hdeg (w, word) = true} ∈ CountingLevel (a + 26) enc := by
    simpa only [decide_eq_true_eq, Nat.add_assoc] using CountingFunction.decision hdec
  convert hlevel using 1
  ext w
  exact C.feasibility_iff_word_witness d hdpos hdeg heven hFn w

/-- Squaring the source polynomial supplies nonnegativity without changing
its evaluation level. This includes non-squarefree inputs and zero arity. -/
theorem feasibility_mem (C : Controlled P enc a) (E : Decoder enc) :
    {w | ∃ x : Fin (n w) → ℝ, eval x ((P w).map (Int.castRingHom ℝ)) = 0} ∈
      CountingLevel (a + 26) enc := by
  let Q := C.mul C
  let d : α → ℕ := fun w => 2 * (Q.degreeBound w + 1)
  have hdpos (w : α) : 1 ≤ d w := by dsimp only [d]; omega
  have hdeg (w : α) : (P w * P w).totalDegree ≤ d w + 1 :=
    (Q.degree_le w).trans (by dsimp only [d]; omega)
  have heven (w : α) : Even (d w + 2) := by
    refine ⟨Q.degreeBound w + 2, ?_⟩
    dsimp only [d]
    omega
  have hd : ComputableInPolyTime d enc encNat :=
    ComputableInPolyTime.binary_mul' (.const 2)
      (ComputableInPolyTime.binary_add' Q.degree_computable (.const 1))
  have hFn (w : α) (x : Fin (n w) → ℝ) :
      0 ≤ eval x ((P w * P w).map (Int.castRingHom ℝ)) := by
    simpa only [map_mul] using mul_self_nonneg (eval x ((P w).map (Int.castRingHom ℝ)))
  have hlevel := Q.nonnegative_feasibility_mem E hdpos hdeg heven hd hFn
  convert hlevel using 1
  ext w
  simp only [map_mul, mul_self_eq_zero]

end LeanCanny.CountingHierarchy.Controlled
