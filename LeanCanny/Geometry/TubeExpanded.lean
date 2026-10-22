/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeProjection
public import LeanCanny.Algebra.ProjectionFlatten

/-! # Ordinary integer polynomials for the parameterized tube system

Expanding the coefficient parameters gives integer polynomials in point,
direction, epsilon, delta, and alpha variables. Evaluation agrees with real
parameter specialization. The total degree bound includes all these variables.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open MvPolynomial
open Algebra.NestedPolynomial
open scoped BigOperators

abbrev IntegerCoordinate (ι : Type*) := Sum (Coordinate ι) Parameter
abbrev IntegerProjectionVariable (ι : Type*) := Sum (Algebra.ProjectionEquations.Variable (Coordinate ι)) Parameter

variable {ι : Type*}

def fullEmbedding : PolynomialPerturbation.Variable ι → IntegerCoordinate ι
  | .inl b => .inr (some b)
  | .inr j => .inl j

theorem flatten_spatial (p : MvPolynomial ι ℤ) :
    flatten (spatial p) = rename (fun i => (.inl (.inl i) : IntegerCoordinate ι)) p := by
  have hc : Int.castRingHom Coefficient = (C : ℤ →+* Coefficient) := Subsingleton.elim _ _
  rw [spatial, hc, flatten_rename, flatten_map_C, rename_rename]
  rfl

theorem flatten_constraint (p : MvPolynomial ι ℤ) (i : PolynomialPerturbation.Constraint ι) :
    flatten (constraint p i) = rename fullEmbedding (PolynomialPerturbation.constraintPolynomial p i) := by
  rcases i with b | ⟨j, b⟩ <;> cases b <;>
    simp [constraint, PolynomialPerturbation.constraintPolynomial, PolynomialPerturbation.spatial,
      flatten_spatial, rename_rename, Function.comp_def, fullEmbedding]

variable [Fintype ι]

theorem flatten_radius : flatten (radius ι) = rename fullEmbedding (PolynomialPerturbation.radiusPolynomial ι) := by
  simp [radius, PolynomialPerturbation.radiusPolynomial, fullEmbedding]

theorem integer_energy_degree (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι)) :
    (flatten (energy p s)).totalDegree ≤ 2 * max p.totalDegree 2 := by
  have hr : (flatten (radius ι)).totalDegree ≤ 2 := by
    rw [flatten_radius]
    exact (totalDegree_rename_le _ _).trans (PolynomialPerturbation.radius_degree ι)
  have hc (i : PolynomialPerturbation.Constraint ι) :
      (flatten (constraint p i)).totalDegree ≤ max p.totalDegree 1 := by
    rw [flatten_constraint]
    exact (totalDegree_rename_le _ _).trans (PolynomialPerturbation.constraint_degree p i)
  simp only [energy, map_add, map_pow, map_sum]
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hr.trans (le_max_right _ _)))
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 ((hc i).trans (max_le_max_left _ (by omega))))

noncomputable def integerPolynomial (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι)) :
    MvPolynomial (IntegerCoordinate ι) ℤ := flatten (polynomial p s)

noncomputable def integerProjection (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (j : ProjectionIndex ι) : MvPolynomial (IntegerProjectionVariable ι) ℤ := flatten (projectionSystem p s j)

theorem integer_polynomial_degree (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι)) :
    (integerPolynomial p s).totalDegree ≤ 2 * max p.totalDegree 2 := by
  simp only [integerPolynomial, polynomial, map_sub, flatten_C_X]
  have h := integer_energy_degree p s
  have hs := totalDegree_sub (flatten (energy p s)) (X (.inr none) : MvPolynomial (IntegerCoordinate ι) ℤ)
  simp only [totalDegree_X] at hs
  omega

theorem integer_projection_degree (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (j : ProjectionIndex ι) : (integerProjection p s j).totalDegree ≤ 2 * max p.totalDegree 2 := by
  apply (Algebra.ProjectionFlatten.system_degree_le (polynomial p s) (base ι) j).trans
  exact max_le (integer_polynomial_degree p s) (by omega)

theorem eval_integerPolynomial (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (x : Coordinate ι → ℝ) :
    (integerPolynomial p s).eval₂ (Int.castRingHom ℝ) (Sum.elim x (parameters epsilon delta alpha)) =
      (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x :=
  eval_flatten (Int.castRingHom ℝ) x (parameters epsilon delta alpha) (polynomial p s)

theorem eval_integerProjection (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (j : ProjectionIndex ι) (epsilon delta alpha : ℝ) (x v : Coordinate ι → ℝ) :
    (integerProjection p s j).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (Sum.elim x v) (parameters epsilon delta alpha)) =
      (projectionSystem p s j).eval₂ (coefficientMap epsilon delta alpha) (Sum.elim x v) :=
  eval_flatten (Int.castRingHom ℝ) (Sum.elim x v) (parameters epsilon delta alpha) (projectionSystem p s j)

theorem integer_projection_variable_count :
    Fintype.card (IntegerProjectionVariable ι) = 7 + 6 * Fintype.card ι := by
  rw [Fintype.card_sum, projection_variable_count]
  simp only [Parameter, Fintype.card_option, Fintype.card_bool]
  omega

def IntegerProjectionInterval (p : MvPolynomial ι ℤ) (epsilon delta a : ℝ) : Prop :=
  ∀ alpha : ℝ, 0 < alpha → alpha < a →
    ∀ (s : Finset (PolynomialPerturbation.Constraint ι)) (x v : Coordinate ι → ℝ),
      v (base ι) = 1 → (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 →
      IsLocalMaxOn (ProjectionCritical.projection v)
        {y | (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y = 0} x →
      ∀ j, (integerProjection p s j).eval₂ (Int.castRingHom ℝ)
        (Sum.elim (Sum.elim x v) (parameters epsilon delta alpha)) = 0

theorem exists_integer_projection_interval (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ IntegerProjectionInterval p epsilon delta a := by
  obtain ⟨a, ha, hr⟩ := exists_projectionInterval p epsilon delta
  refine ⟨a, ha, ?_⟩
  intro alpha hp hs s x v hv hx hmax j
  rw [eval_integerProjection]
  exact hr alpha hp hs s x v hv hx hmax j

end LeanCanny.Geometry.TubePolynomial
