/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeRegularity
public import LeanCanny.Geometry.TubeDegree
public import LeanCanny.Geometry.ProjectionCritical

/-! # Projection equations for the actual active tubes

A root-shift coordinate supplies a base coordinate even when the original ETR
input has no spatial variables. The projection system has one equation per
point coordinate, over the integer polynomial parameter ring.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial

variable {ι : Type*} [Fintype ι]

def base (ι : Type*) : Coordinate ι := .inr (.inl false)
abbrev ProjectionIndex (ι : Type*) := Algebra.ProjectionEquations.Index (base ι)

noncomputable def projectionSystem (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (j : ProjectionIndex ι) : MvPolynomial (Algebra.ProjectionEquations.Variable (Coordinate ι)) Coefficient :=
  Algebra.ProjectionEquations.system (polynomial p s) (base ι) j

theorem projection_degree (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (j : ProjectionIndex ι) : (projectionSystem p s j).totalDegree ≤ 2 * max p.totalDegree 2 := by
  apply (Algebra.ProjectionEquations.system_degree_le (polynomial p s) (base ι) j).trans
  exact max_le (polynomial_degree p s) (by omega)

theorem projection_count [DecidableEq ι] : Fintype.card (ProjectionIndex ι) = 2 + 3 * Fintype.card ι := by
  rw [Algebra.ProjectionEquations.system_card]
  simp only [Coordinate, PolynomialPerturbation.Constraint, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  omega

theorem projection_variable_count :
    Fintype.card (Algebra.ProjectionEquations.Variable (Coordinate ι)) = 4 + 6 * Fintype.card ι := by
  simp only [Algebra.ProjectionEquations.Variable, Coordinate, PolynomialPerturbation.Constraint,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  omega

theorem exists_projection_interval (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∀ (s : Finset (PolynomialPerturbation.Constraint ι)) (x v : Coordinate ι → ℝ),
        v (base ι) = 1 → (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 →
        IsLocalMaxOn (ProjectionCritical.projection v)
          {y | (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y = 0} x →
        ∀ j, (projectionSystem p s j).eval₂ (coefficientMap epsilon delta alpha) (Sum.elim x v) = 0 := by
  obtain ⟨a, ha, hr⟩ := exists_common_regular_interval p epsilon delta
  refine ⟨a, ha, ?_⟩
  intro alpha hp hs s x v hv hx hmax
  exact ProjectionCritical.satisfies_system _ _ (base ι) x v hv hx hmax (hr alpha hp hs s x hx)

def ProjectionInterval (p : MvPolynomial ι ℤ) (epsilon delta a : ℝ) : Prop :=
  ∀ alpha : ℝ, 0 < alpha → alpha < a →
    ∀ (s : Finset (PolynomialPerturbation.Constraint ι)) (x v : Coordinate ι → ℝ),
      v (base ι) = 1 → (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 →
      IsLocalMaxOn (ProjectionCritical.projection v)
        {y | (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y = 0} x →
      ∀ j, (projectionSystem p s j).eval₂ (coefficientMap epsilon delta alpha) (Sum.elim x v) = 0

theorem exists_projectionInterval (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ProjectionInterval p epsilon delta a := exists_projection_interval p epsilon delta

end LeanCanny.Geometry.TubePolynomial
