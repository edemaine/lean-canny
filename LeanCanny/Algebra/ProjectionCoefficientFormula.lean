/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectionFlatten
public import LeanCanny.Algebra.EmbeddedCoefficient

/-! # Projection coefficients from two shifted source coefficients

After flattening, the level row is an injective variable embedding. A partial
row uses two embedded derivatives, with one direction-variable shift. Each
derivative coefficient is one source coefficient times its integer exponent.
Thus no dense polynomial product is needed for projection coefficient access.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionFlatten
open MvPolynomial NestedPolynomial

variable {σ τ R : Type*} [CommRing R]

def coefficientEmbedding : Sum σ τ → Sum (Sum σ σ) τ := Sum.map Sum.inl id

theorem coefficientEmbedding_injective : Function.Injective (coefficientEmbedding (σ := σ) (τ := τ)) :=
  Sum.inl_injective.sumMap Function.injective_id

theorem coeff_level (p : MvPolynomial σ (MvPolynomial τ R)) (base : σ)
    (m : Sum (Sum σ σ) τ →₀ ℕ) :
    (flatten (ProjectionEquations.polynomial p base none)).coeff m =
      EmbeddedCoefficient.value coefficientEmbedding coefficientEmbedding_injective (flatten p) m := by
  rw [level]
  exact EmbeddedCoefficient.coeff_rename coefficientEmbedding coefficientEmbedding_injective (flatten p) m

noncomputable def shiftedDerivative (p : MvPolynomial (Sum σ τ) R) (base i : σ)
    (m : Sum (Sum σ σ) τ →₀ ℕ) : R := by
  classical
  exact if (.inl (.inr i) : Sum (Sum σ σ) τ) ∈ m.support then
    EmbeddedCoefficient.derivative coefficientEmbedding coefficientEmbedding_injective p (.inl base)
      (m - Finsupp.single (.inl (.inr i)) 1) else 0

theorem coeff_partial (p : MvPolynomial σ (MvPolynomial τ R)) (base i : σ)
    (m : Sum (Sum σ σ) τ →₀ ℕ) :
    (flatten (ProjectionEquations.polynomial p base (some i))).coeff m =
      EmbeddedCoefficient.derivative coefficientEmbedding coefficientEmbedding_injective (flatten p) (.inl i) m -
        shiftedDerivative (flatten p) base i m := by
  classical
  rw [partial_eq, MvPolynomial.coeff_sub, MvPolynomial.coeff_X_mul']
  have hi := EmbeddedCoefficient.coeff_rename_pderiv
    (coefficientEmbedding (σ := σ) (τ := τ)) coefficientEmbedding_injective (flatten p) (.inl i) m
  have hb := EmbeddedCoefficient.coeff_rename_pderiv
    (coefficientEmbedding (σ := σ) (τ := τ)) coefficientEmbedding_injective (flatten p) (.inl base)
    (m - Finsupp.single (.inl (.inr i)) 1)
  unfold coefficientEmbedding at hi hb
  rw [hi, hb]
  rfl

end LeanCanny.Algebra.ProjectionFlatten
