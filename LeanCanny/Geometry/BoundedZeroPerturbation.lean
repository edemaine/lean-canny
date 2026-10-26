/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.BoundedZeroComponents
public import LeanCanny.Geometry.BoundedPositivePerturbation

/-! # A component-preserving pure-power perturbation of bounded polynomial zeros

The sphere source supplies nonnegativity, compact sublevels, degree and mass
controls, and a uniform zero-set radius. The resulting dyadic perturbation
preserves the bounded original component relation at every level in the upper
half of its safe interval. Choosing a regular level and recovering original
paths are separate tasks.
-/

@[expose] public section
namespace LeanCanny.Geometry.BoundedZeroSource
open MvPolynomial Set LeanCanny.Algebra
open scoped BigOperators

variable {n : ℕ}

def penaltyExponent (n D R : ℕ) : ℕ := R * powerDegree D + (n + 2).size

def perturbationExponent (n D b R : ℕ) : ℕ :=
  BoundedPositivePerturbation.exponent (n + 2) (degreeAllowance D) (massExponent n b R) (penaltyExponent n D R)

noncomputable def perturbationCoefficient (n D b R : ℕ) : ℝ := InfinitesimalSign.dyadic (perturbationExponent n D b R)

noncomputable def tolerance (n D b R : ℕ) : ℝ :=
  GeneralCriticalValueBounds.level (n + 2) (degreeAllowance D) (massExponent n b R)

theorem component_iff_perturbed (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b)
    (a : ℝ) (ha : tolerance n D b R / 2 ≤ a) (haδ : a ≤ tolerance n D b R)
    (x y : Bounded q R) :
    y.val ∈ connectedComponentIn (Bounded q R) x.val ↔
      (sectionMap q R y).val ∈ connectedComponentIn
        {w : Fin (n + 2) → ℝ | (polynomial q R).eval₂ (Int.castRingHom ℝ) w +
          perturbationCoefficient n D b R * ∑ i : Fin (n + 2), w i ^ powerDegree D ≤ a}
        (sectionMap q R x).val := by
  have hs : y.val ∈ connectedComponentIn (Bounded q R) x.val ↔
      (sectionMap q R y).val ∈ connectedComponentIn (Zeros q R) (sectionMap q R x).val := by
    rw [← section_component_iff, connectedComponentIn_eq_image (sectionMap q R x).property]
    constructor
    · intro h
      exact ⟨sectionMap q R y, h, rfl⟩
    · rintro ⟨z, hz, he⟩
      exact (Subtype.ext he : z = sectionMap q R y) ▸ hz
  exact hs.trans (BoundedPositivePerturbation.component_iff_power_perturbed (polynomial q R)
    (degreeAllowance D) (massExponent n b R) (powerDegree D) R (degree_bound q D R hD)
    (by unfold degreeAllowance; omega) (mass_bound q b R hb) (nonneg q R) (compact_sublevels q R)
    (powerDegree_even D) (zero_coordinate_bound q R) a ha haδ
    (sectionMap q R x).val (sectionMap q R y).val (sectionMap q R x).property (sectionMap q R y).property)

end LeanCanny.Geometry.BoundedZeroSource
