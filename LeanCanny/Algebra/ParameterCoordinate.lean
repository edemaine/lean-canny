/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicScaledSquarefreeSmall
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # Moving the first polynomial variable into a symbolic coefficient -/

@[expose] public section
namespace LeanCanny.Algebra.ParameterCoordinate
open MvPolynomial
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

noncomputable def move : MvPolynomial (Fin (n + 1)) ℤ →+* MvPolynomial (Fin n) (Polynomial ℤ) :=
  eval₂Hom (Int.castRingHom _) (Fin.cons (C Polynomial.X) X)

theorem eval_move (p : MvPolynomial (Fin (n + 1)) ℤ) (s : ℝ) (x : Fin n → ℝ) :
    (move p).eval₂ (SymbolicScaledSquarefree.scalarEvaluation s) x =
      p.eval₂ (Int.castRingHom ℝ) (Fin.cons s x) := by
  let phi := eval₂Hom (SymbolicScaledSquarefree.scalarEvaluation s) x
  change phi (move p) = _
  have he : phi.comp move = eval₂Hom (Int.castRingHom ℝ) (Fin.cons s x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [phi, move]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [phi, move, SymbolicScaledSquarefree.scalarEvaluation]
      · simp [phi, move]
  exact congrArg (fun f : MvPolynomial (Fin (n + 1)) ℤ →+* ℝ => f p) he

end LeanCanny.Algebra.ParameterCoordinate
