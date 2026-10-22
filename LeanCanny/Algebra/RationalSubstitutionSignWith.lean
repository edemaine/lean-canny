/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionWith

/-! # Uniform clearing allowances preserve signs under specialization -/

@[expose] public section
namespace LeanCanny.Algebra.RationalSubstitution
open Polynomial
open scoped BigOperators Classical
variable {σ R : Type*} [Fintype σ] [CommSemiring R]

theorem sign_eval₂_clearedWith (φ : R →+* ℝ) (x : ℝ)
    (D : σ → ℕ) (p : MvPolynomial σ R) (n d : σ → R[X])
    (hD : ∀ i, p.degreeOf i ≤ D i) (hd : ∀ i, (d i).eval₂ φ x ≠ 0) :
    SignType.sign ((clearedWith D p n d).eval₂ φ x) =
      SignType.sign (p.eval₂ φ (fun i => (n i).eval₂ φ x / (d i).eval₂ φ x)) := by
  rw [eval₂_clearedWith φ x D p n d hD hd, sign_mul]
  have hp : 0 < ∏ i, (d i).eval₂ φ x ^ (2 * D i) := by
    apply Finset.prod_pos
    intro i _
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero (hd i)) _
  rw [sign_pos hp, one_mul]

end LeanCanny.Algebra.RationalSubstitution
