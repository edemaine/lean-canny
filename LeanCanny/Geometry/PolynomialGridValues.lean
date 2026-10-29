/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialValueSpecialization
public import LeanCanny.Geometry.AlgebraicBranchZero
public import LeanCanny.Geometry.UnivariateRootFamily

/-! # Constructed polynomial-value annihilators on coordinate grids

Nonzero coordinate equations imply algebraicity of all generic grid points.
Every polynomial test therefore has a nonzero value annihilator. Its
trailing coefficient excludes finitely many real parameters, outside which
zero tests are constant on continuous branches. Multiplicities in the grid
equations require no regularity assumption. Quantitative certificate bounds
and coefficient readers remain open.
-/

@[expose] public section
namespace LeanCanny.Geometry.PolynomialGridValues
open LeanCanny.Algebra MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def value (q : κ → MvPolynomial ι (Polynomial ℝ))
    (z : ℝ × (ι → ℝ)) : κ → ℝ := fun k => (q k).eval₂ (Polynomial.evalRingHom z.1) z.2

omit [Fintype κ] in
lemma continuous_value (q : κ → MvPolynomial ι (Polynomial ℝ)) : Continuous (value q) :=
  continuous_pi (fun k => (PolynomialRootFamily.contDiff_eval (q k) 1).continuous)

/-- The returned relations hold at every parameter. Only constancy of their
zero tests needs removal of the finite trailing-coefficient root set. -/
theorem exists_annihilators (p : ι → Polynomial (Polynomial ℝ)) (hp : ∀ i, p i ≠ 0)
    (q : κ → MvPolynomial ι (Polynomial ℝ)) :
    ∃ Q : κ → Polynomial (Polynomial ℝ), (∀ k, Q k ≠ 0) ∧
      {t : ℝ | ∃ k, (Q k).trailingCoeff.eval t = 0}.Finite ∧
      ∀ t x, (∀ i, (p i).eval₂ (Polynomial.evalRingHom t) (x i) = 0) →
        ∀ k, (Q k).eval₂ (Polynomial.evalRingHom t) (value q (t, x) k) = 0 := by
  have h (k : κ) := PolynomialValueSpecialization.exists_grid_value_annihilator
    (F := FractionRing (Polynomial ℝ)) p hp (q k)
  choose Q hQ hm using h
  refine ⟨Q, hQ, ?_, ?_⟩
  · exact (Set.finite_iUnion (fun k => AlgebraicBranchZero.finite_exceptional (Q k) (hQ k))).subset
      (fun _ ht => Set.mem_iUnion.mpr ht)
  · intro t x hx k
    apply PolynomialValueSpecialization.eval_annihilator _ (q k) (Q k) (hm k)
      (Polynomial.evalRingHom t) x
    have hI : PolynomialValueSpecialization.gridIdeal p ≤
        RingHom.ker (MvPolynomial.eval₂Hom (Polynomial.evalRingHom t) x) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change ((p i).toMvPolynomial i).eval₂ (Polynomial.evalRingHom t) x = 0
      rw [UnivariateRootFamily.eval]
      exact hx i
    exact fun u hu => hI hu

end LeanCanny.Geometry.PolynomialGridValues
