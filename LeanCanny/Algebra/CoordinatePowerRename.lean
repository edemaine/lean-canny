/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinatePowerSubstitution

/-! # Power substitution through a variable embedding

Bounds for a spatial block use only that block's powers, independently of
the larger powers assigned to old scalar parameters or multipliers.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoordinatePowerSubstitution
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {σ τ R : Type*} [CommSemiring R]

theorem rename (w : τ → ℕ) (f : σ → τ) (p : MvPolynomial σ R) :
    substitute w (MvPolynomial.rename f p) = MvPolynomial.rename f (substitute (w ∘ f) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [rename_C, substitute_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, rename_X, substitute_X, map_pow, Function.comp_apply]

theorem rename_degree [Fintype σ] (w : τ → ℕ) (f : σ → τ) (p : MvPolynomial σ R)
    (W : ℕ) (hw : ∀ i, w (f i) ≤ W) :
    (substitute w (MvPolynomial.rename f p)).totalDegree ≤ W * p.totalDegree := by
  rw [rename]
  exact (totalDegree_rename_le _ _).trans (degree_le (w ∘ f) p W hw)

end LeanCanny.Algebra.CoordinatePowerSubstitution
