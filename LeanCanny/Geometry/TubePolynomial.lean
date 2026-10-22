/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PerturbationPolynomials
public import LeanCanny.Geometry.ActiveRadiusCritical
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-! # Polynomial tubes around the active perturbed constraints

The coefficient ring carries epsilon, delta, and alpha. Point and shift
coordinates are the polynomial variables. The tube is the sum of squares of
the active shifted constraints and the radius equation, minus alpha.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open MvPolynomial
open scoped BigOperators

abbrev Parameter := Option Bool
abbrev Coefficient := MvPolynomial Parameter ℤ
abbrev Coordinate (ι : Type*) := Sum ι (PolynomialPerturbation.Constraint ι)

def parameters (epsilon delta alpha : ℝ) : Parameter → ℝ
  | none => alpha
  | some false => epsilon
  | some true => delta

noncomputable def coefficientMap (epsilon delta alpha : ℝ) : Coefficient →+* ℝ :=
  eval₂Hom (Int.castRingHom ℝ) (parameters epsilon delta alpha)

variable {ι : Type*}

def point (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) : Coordinate ι → ℝ :=
  Sum.elim z.1 z.2

def splitPoint (x : Coordinate ι → ℝ) : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ) :=
  (fun i => x (.inl i), fun i => x (.inr i))

theorem point_splitPoint (x : Coordinate ι → ℝ) : point (splitPoint x) = x := by
  funext i
  cases i <;> rfl

noncomputable def spatial (p : MvPolynomial ι ℤ) : MvPolynomial (Coordinate ι) Coefficient :=
  rename Sum.inl (p.map (Int.castRingHom Coefficient))

noncomputable def constraint (p : MvPolynomial ι ℤ) :
    PolynomialPerturbation.Constraint ι → MvPolynomial (Coordinate ι) Coefficient
  | .inl false => spatial p + X (.inr (.inl false))
  | .inl true => -spatial p + X (.inr (.inl true))
  | .inr (i, false) => X (.inl i) + 1 - C (X (some false)) + X (.inr (.inr (i, false)))
  | .inr (i, true) => 1 - C (X (some false)) - X (.inl i) + X (.inr (.inr (i, true)))

theorem eval_spatial (p : MvPolynomial ι ℤ) (epsilon delta alpha : ℝ)
    (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) :
    (spatial p).eval₂ (coefficientMap epsilon delta alpha) (point z) = p.eval₂ (Int.castRingHom ℝ) z.1 := by
  rw [spatial, eval₂_rename, eval₂_map]
  have h : (coefficientMap epsilon delta alpha).comp (Int.castRingHom Coefficient) = Int.castRingHom ℝ := by
    ext n
    simp
  rw [h]
  rfl

theorem eval_constraint (p : MvPolynomial ι ℤ) (epsilon delta alpha : ℝ)
    (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) (i : PolynomialPerturbation.Constraint ι) :
    (constraint p i).eval₂ (coefficientMap epsilon delta alpha) (point z) =
      PolynomialPerturbation.parameterMap p epsilon z i := by
  rcases i with b | ⟨j, b⟩
  · cases b
    · rw [constraint, eval₂_add, eval_spatial, eval₂_X]
      rfl
    · rw [constraint, eval₂_add, eval₂_neg, eval_spatial, eval₂_X]
      rfl
  · cases b <;>
      simp only [constraint, eval₂_add, eval₂_sub, eval₂_one, eval₂_X, eval₂_C,
        point, Sum.elim_inl, Sum.elim_inr, coefficientMap, eval₂Hom_X', parameters,
        PolynomialPerturbation.parameterMap, PolynomialPerturbation.value]

variable [Fintype ι]

noncomputable def radius (ι : Type*) [Fintype ι] : MvPolynomial (Coordinate ι) Coefficient :=
  (∑ i : PolynomialPerturbation.Constraint ι, X (.inr i) ^ 2) - C (X (some true)) ^ 2

noncomputable def energy (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι)) :
    MvPolynomial (Coordinate ι) Coefficient := radius ι ^ 2 + ∑ i ∈ s, constraint p i ^ 2

noncomputable def polynomial (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι)) :
    MvPolynomial (Coordinate ι) Coefficient := energy p s - C (X none)

theorem eval_radius (epsilon delta alpha : ℝ)
    (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) :
    (radius ι).eval₂ (coefficientMap epsilon delta alpha) (point z) = SquaredRadius.value z.2 - delta ^ 2 := by
  simp only [radius, eval₂_sub, eval₂_sum, eval₂_pow, eval₂_X, eval₂_C,
    point, Sum.elim_inr, coefficientMap, eval₂Hom_X', parameters, SquaredRadius.value]

theorem eval_energy (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) :
    (energy p s).eval₂ (coefficientMap epsilon delta alpha) (point z) =
      (SquaredRadius.value z.2 - delta ^ 2) ^ 2 + ∑ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i ^ 2 := by
  simp only [energy, eval₂_add, eval₂_sum, eval₂_pow, eval_radius, eval_constraint]

theorem eval_polynomial (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) :
    (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) (point z) =
      (SquaredRadius.value z.2 - delta ^ 2) ^ 2 +
        (∑ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i ^ 2) - alpha := by
  rw [polynomial, eval₂_sub, eval_energy, eval₂_C]
  simp only [coefficientMap, eval₂Hom_X', parameters]

theorem zero_level_iff (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) :
    (polynomial p s).eval₂ (coefficientMap epsilon delta 0) (point z) = 0 ↔
      SquaredRadius.value z.2 = delta ^ 2 ∧ ∀ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i = 0 := by
  rw [eval_polynomial, sub_zero, add_eq_zero_iff_of_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _), sq_eq_zero_iff, sub_eq_zero,
    Finset.sum_sq_eq_zero_iff]

end LeanCanny.Geometry.TubePolynomial
